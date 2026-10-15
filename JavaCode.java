import java.io.BufferedReader;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;
import java.util.TreeMap;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.stream.Collectors;

/*
 * ============================================================
 *  HOSPITAL EMERGENCY ROOM TRIAGE SYSTEM   (Team No - 06)
 *  Rule-based Java program that ranks arriving patients by
 *  urgency so the most critical are seen first.
 *
 *  Run in VS Code:   javac TriageSystem.java
 *                    java TriageSystem
 *  (or press the "Run" button above main in VS Code)
 * ============================================================
 */

public class TriageSystem {

    // ---------- MODULE 1: constants ----------
    static final int MAX_PATIENTS = 50;
    static final int FIELD_COUNT = 6;                       // name,age,hr,spo2,temp,conscious
    static final Path DATA_FILE = Path.of("patients.csv");

    // bitwise alert flags
    static final int TACHYCARDIA = 1;     // 0001
    static final int HYPOXIA     = 2;     // 0010
    static final int FEVER       = 4;     // 0100
    static final int UNCONSCIOUS = 8;     // 1000

    // ---------- MODULE 6: collections ----------
    static List<Patient> queue = new ArrayList<>();
    static Map<Integer, Patient> byId = new HashMap<>();

    static Scanner sc = new Scanner(System.in);

    // =====================================================
    //  MODULE 3: Methods (score rules) + overloading
    // =====================================================
    static int calcScore(int hr, int spo2, double temp) {
        return calcScore(hr, spo2, temp, 30);               // default adult age
    }

    static int calcScore(int hr, int spo2, double temp, int age) {
        int score = 0;

        // heart rate points (ternary + relational + logical operators)
        score += (hr > 130 || hr < 40) ? 3 : 0;
        score += ((hr > 110 && hr <= 130) || (hr >= 40 && hr < 50)) ? 2 : 0;
        score += (hr > 100 && hr <= 110) ? 1 : 0;

        // oxygen saturation points
        if (spo2 < 90) score += 3;
        else if (spo2 < 94) score += 2;
        else if (spo2 < 96) score += 1;

        // temperature points
        if (temp >= 39.5 || temp < 35.0) score += 2;
        else if (temp >= 38.0) score += 1;

        // combined risk: fever together with low oxygen
        if (temp >= 38 && spo2 < 94) score++;

        // very young or elderly patients are more fragile
        if (age >= 65 || age <= 5) score++;

        return score;
    }

    // MODULE 2: if-else-if ladder + nested if (safety override)
    static int levelFromScore(int score, int spo2, boolean conscious) {
        int level;
        if (score >= 9) level = 1;
        else if (score >= 6) level = 2;
        else if (score >= 4) level = 3;
        else if (score >= 2) level = 4;
        else level = 5;

        // nested if: safety override
        if (spo2 < 90) {
            if (!conscious) level = 1;
        }
        return level;
    }

    // MODULE 2: switch
    static String levelLabel(int level) {
        String label;
        switch (level) {
            case 1:  label = "IMMEDIATE";  break;
            case 2:  label = "EMERGENT";   break;
            case 3:  label = "URGENT";     break;
            case 4:  label = "LESS URGENT"; break;
            default: label = "NON-URGENT";
        }
        return label;
    }

    static int targetMinutes(int level) {
        switch (level) {
            case 1:  return 0;
            case 2:  return 10;
            case 3:  return 30;
            case 4:  return 60;
            default: return 120;
        }
    }

    // MODULE 4: throws / throw (checked exception)
    static void checkVitals(int age, int hr, int spo2, double temp) throws InvalidVitalsException {
        if (age < 0 || age > 120)
            throw new InvalidVitalsException("Age must be 0-120");
        if (hr < 20 || hr > 250)
            throw new InvalidVitalsException("Heart rate must be 20-250 bpm");
        if (spo2 < 50 || spo2 > 100)
            throw new InvalidVitalsException("SpO2 must be 50-100 %");
        if (temp < 30.0 || temp > 45.0)
            throw new InvalidVitalsException("Temperature must be 30-45 C");
    }

    // Bitwise operators: build alert flags
    static int alertFlags(Patient p) {
        int flags = 0;
        if (p.getHeartRate() > 110) flags |= TACHYCARDIA;
        if (p.getSpo2() < 94)       flags |= HYPOXIA;
        if (p.getTemp() >= 38.0)    flags |= FEVER;
        if (!p.isConscious())       flags |= UNCONSCIOUS;
        return flags;
    }

    static String describeFlags(int flags) {
        if (flags == 0) return "none";
        StringBuilder sb = new StringBuilder();
        if ((flags & TACHYCARDIA) != 0) sb.append("TACHYCARDIA ");
        if ((flags & HYPOXIA) != 0)     sb.append("HYPOXIA ");
        if ((flags & FEVER) != 0)       sb.append("FEVER ");
        if ((flags & UNCONSCIOUS) != 0) sb.append("UNCONSCIOUS ");
        return sb.toString().trim();
    }

    // Factory: critical patients become CriticalPatient objects (polymorphism)
    static Patient createPatient(String name, int age, int hr, int spo2, double temp, boolean conscious)
            throws InvalidVitalsException {
        checkVitals(age, hr, spo2, temp);
        int level = levelFromScore(calcScore(hr, spo2, temp, age), spo2, conscious);
        if (level == 1) {
            return new CriticalPatient(name, age, hr, spo2, temp, conscious);
        }
        return new Patient(name, age, hr, spo2, temp, conscious);
    }

    // =====================================================
    //  Overloaded print() methods (quick and detailed)
    // =====================================================
    static void print(String name, int level) {
        System.out.printf("%-12s Level:%d (%s)%n", name, level, levelLabel(level));
    }

    static void print(String name, int level, int wait) {
        System.out.printf("%-12s Level:%d (%-11s) Waiting: %3d min%n", name, level, levelLabel(level), wait);
    }

    static void print(Patient p) {
        System.out.printf("%-4d %-12s Age:%3d HR:%3d SpO2:%3d Temp:%4.1f Score:%2d Level:%d %-11s Wait:%3d min%n",
                p.getId(), p.getName(), p.getAge(), p.getHeartRate(), p.getSpo2(), p.getTemp(),
                p.calcScore(), p.getLevel(), levelLabel(p.getLevel()), p.getWait());
    }

    // =====================================================
    //  CONSOLE INPUT HELPERS  (MODULE 2 loops + MODULE 4 exceptions)
    // =====================================================
    static int readInt(String prompt, int min, int max) {
        int value = 0;
        boolean ok;
        do {                                    // do-while: ask at least once
            System.out.print(prompt);
            String s = sc.nextLine();
            try {
                value = Integer.parseInt(s.trim());
                ok = (value >= min && value <= max);
                if (!ok) System.out.println("  Enter a value between " + min + " and " + max + ".");
            } catch (NumberFormatException | NullPointerException ex) {   // multi-catch
                System.out.println("  Invalid input, please enter a number.");
                ok = false;
            }
        } while (!ok);
        return value;
    }

    static double readDouble(String prompt, double min, double max) {
        double value = 0;
        boolean ok;
        do {
            System.out.print(prompt);
            String s = sc.nextLine();
            try {
                value = Double.parseDouble(s.trim());
                ok = (value >= min && value <= max);
                if (!ok) System.out.println("  Enter a value between " + min + " and " + max + ".");
            } catch (NumberFormatException ex) {
                System.out.println("  Invalid input, please enter a number.");
                ok = false;
            }
        } while (!ok);
        return value;
    }

    static boolean readYesNo(String prompt) {
        while (true) {
            System.out.print(prompt + " (Y/N): ");
            String ans = sc.nextLine().trim().toUpperCase();
            if (ans.startsWith("Y")) return true;
            if (ans.startsWith("N")) return false;
            System.out.println("  Please type Y or N.");
        }
    }

    // =====================================================
    //  MENU ACTIONS
    // =====================================================
    static void registerPatient() {
        if (queue.size() >= MAX_PATIENTS) {
            System.out.println("Queue is full (max " + MAX_PATIENTS + ").");
            return;
        }
        System.out.print("Patient name: ");
        String name = sc.nextLine().trim();          // Strings: trim()
        if (name.isEmpty()) {
            System.out.println("Name cannot be empty.");
            return;
        }
        int age = readInt("Age (0-120): ", 0, 120);
        int hr = readInt("Heart rate (bpm): ", 20, 250);
        int spo2 = readInt("SpO2 (%): ", 50, 100);
        double temp = readDouble("Temperature (C): ", 30.0, 45.0);
        boolean conscious = readYesNo("Is the patient conscious?");

        try {
            Patient p = createPatient(name, age, hr, spo2, temp, conscious);
            System.out.print("Allergy (press Enter to skip): ");
            String allergy = sc.nextLine().trim();
            if (!allergy.isEmpty()) p.addAllergy(allergy);

            queue.add(p);
            byId.put(p.getId(), p);
            System.out.println();
            System.out.println("Registered -> " + p);
            print(p.getName(), p.getLevel());
            System.out.println("Target time to treatment: " + targetMinutes(p.getLevel()) + " min");
            System.out.println("Alerts: " + describeFlags(alertFlags(p)));
        } catch (InvalidVitalsException ex) {
            System.out.println("Rejected: " + ex.getMessage());
        } finally {
            System.out.println("Registration step finished.");
        }
    }

    static void showQueue() {
        Collections.sort(queue);                      // Comparable: level, then wait
        boolean any = false;
        System.out.println();
        System.out.println("---------------- WAITING QUEUE ----------------");
        for (int i = 0; i < queue.size(); i++) {      // for loop
            Patient p = queue.get(i);
            if (p.isDone()) continue;                 // continue: skip discharged
            any = true;
            System.out.print((i + 1) + ". ");
            print(p);
        }
        if (!any) System.out.println("No patients waiting.");
    }

    static void callNext() {
        Collections.sort(queue);
        for (Patient p : queue) {
            if (!p.isDone()) {
                p.markDone();
                System.out.println("Calling next patient: " + p);
                print(p.getName(), p.getLevel(), p.getWait());
                return;
            }
        }
        System.out.println("No patients waiting.");
    }

    static void searchPatient() {
        int id = readInt("Enter patient ID: ", 1, 999999);
        Patient p = byId.get(id);                     // HashMap lookup
        if (p == null) {                              // null reference check
            System.out.println("No patient with ID " + id);
        } else {
            print(p);
            System.out.println("   Alerts: " + describeFlags(alertFlags(p)));
            System.out.println("   Allergies: " + (p.getAllergies().isEmpty() ? "none" : p.getAllergies()));
            System.out.println("   Status: " + (p.isDone() ? "Treated" : "Waiting"));
        }
    }

    static void advanceClock() {
        int m = readInt("Minutes to advance (1-240): ", 1, 240);
        for (Patient p : queue) {
            if (!p.isDone()) p.addWait(m);
        }
        System.out.println("Waiting times updated.");
    }

    static void removeTreated() {
        int removed = 0;
        Iterator<Patient> it = queue.iterator();      // Iterator
        while (it.hasNext()) {
            Patient p = it.next();
            if (p.isDone()) {
                byId.remove(p.getId());
                it.remove();
                removed++;
            }
        }
        System.out.println("Removed " + removed + " treated patient(s) from the list.");
    }

    // =====================================================
    //  REPORTS: arrays, matrices, streams, StringBuilder
    // =====================================================
    static void showReport() {
        List<Patient> waiting = queue.stream()
                .filter(p -> !p.isDone())
                .collect(Collectors.toList());

        System.out.println();
        System.out.println("================ SHIFT REPORT ================");
        System.out.println("Patients registered : " + Patient.getTotal());
        System.out.println("Currently waiting   : " + waiting.size());

        // ----- Streams: lambdas + functional interfaces -----
        Predicate<Patient> critical = p -> p.getLevel() == 1;
        Predicate<Patient> activeCritical = critical.and(p -> !p.isDone());
        Function<Patient, String> nm = Patient::getName;
        Comparator<Patient> byWait = Comparator.comparingInt(Patient::getWait);
        Consumer<Patient> show = p -> print(p.getName(), p.getLevel(), p.getWait());
        Supplier<String> heading = () -> "Critical patients, longest waiting first";

        long criticalCount = queue.stream().filter(activeCritical).count();
        System.out.println("Critical waiting    : " + criticalCount);

        System.out.println(heading.get() + " (top 3):");
        queue.stream()
                .filter(activeCritical)
                .sorted(byWait.reversed())
                .limit(3)
                .map(nm)
                .forEach(System.out::println);

        System.out.println("Everyone waiting (Consumer):");
        waiting.forEach(show);

        // Collectors.groupingBy + counting
        Map<Integer, Long> perLevelStream = waiting.stream()
                .collect(Collectors.groupingBy(Patient::getLevel, TreeMap::new, Collectors.counting()));
        System.out.println("Waiting per level (stream) : " + perLevelStream);

        // TreeMap + merge (keys kept sorted)
        Map<Integer, Integer> perLevel = new TreeMap<>();
        for (Patient p : waiting) {
            perLevel.merge(p.getLevel(), 1, Integer::sum);
        }
        for (var en : perLevel.entrySet()) {
            System.out.println("  Level " + en.getKey() + " -> " + en.getValue() + " patient(s)");
        }

        // Collectors.joining
        String names = waiting.stream().map(nm).distinct().collect(Collectors.joining(", "));
        System.out.println("Names waiting : " + (names.isEmpty() ? "none" : names));

        // Autoboxing + reduce
        List<Integer> waits = new ArrayList<>();
        for (Patient p : waiting) {
            waits.add(p.getWait());                   // autoboxing
        }
        int totalWait = waits.stream().reduce(0, Integer::sum);
        double avg = waits.isEmpty() ? 0.0 : (double) totalWait / waits.size();   // typecasting
        System.out.printf("Total wait: %d min | Average wait: %.1f min%n", totalWait, avg);

        // StringBuilder report line
        StringBuilder sb = new StringBuilder();
        for (Patient p : waiting) {
            sb.append(p.getName()).append(" L").append(p.getLevel()).append(" | ");
        }
        if (sb.length() > 0) sb.setLength(sb.length() - 3);
        sb.insert(0, "> ");
        System.out.println(sb);
    }

    // MODULE 3: 1D array statistics
    static void showArrayDemo() {
        int[] waitTimes = {12, 45, 8, 30, 22};        // minutes
        int sum = 0, longest = waitTimes[0], over30 = 0;
        for (int w : waitTimes) {
            sum += w;
            if (w > longest) longest = w;
            if (w > 30) over30++;
        }
        double average = (double) sum / waitTimes.length;

        System.out.println();
        System.out.println("---- 1D ARRAY: sample waiting times ----");
        System.out.println("Waits    : " + Arrays.toString(waitTimes));
        System.out.printf("Average  : %.1f min%n", average);
        System.out.println("Sum      : " + sum + " min");
        System.out.println("Longest  : " + longest + " min");
        System.out.println("Over 30  : " + over30);

        Arrays.sort(waitTimes);                       // library sort
        System.out.println("Sorted   : " + Arrays.toString(waitTimes));
        int pos = Arrays.binarySearch(waitTimes, 30); // array must be sorted
        System.out.println("Index of 30 after sorting: " + pos);
    }

    // MODULE 3: 2D arrays and matrix addition
    static void showMatrixDemo() {
        String[] shifts = {"Morning", "Evening", "Night"};
        int[][] day1 = {
                {1, 3, 6, 8, 4},
                {2, 4, 7, 9, 5},
                {1, 2, 5, 4, 2}
        };
        int[][] day2 = {
                {0, 4, 5, 7, 6},
                {1, 5, 8, 6, 3},
                {2, 1, 4, 5, 1}
        };
        int[][] total = new int[3][5];

        for (int i = 0; i < 3; i++) {
            for (int j = 0; j < 5; j++) {
                total[i][j] = day1[i][j] + day2[i][j];
            }
        }

        System.out.println();
        System.out.println("---- 2D ARRAY: arrivals per shift and level ----");
        printMatrix("Day 1 Arrivals", shifts, day1);
        printMatrix("Day 2 Arrivals", shifts, day2);
        printMatrix("Total = Day1 + Day2", shifts, total);
    }

    static void printMatrix(String title, String[] rows, int[][] m) {
        System.out.println(title);
        System.out.printf("%-9s %4s %4s %4s %4s %4s%n", "", "L1", "L2", "L3", "L4", "L5");
        for (int i = 0; i < m.length; i++) {
            System.out.printf("%-9s", rows[i]);
            for (int j = 0; j < m[i].length; j++) {
                System.out.printf(" %4d", m[i][j]);
            }
            System.out.println();
        }
        System.out.println();
    }

    // MODULE 5: String parsing demo + equals vs ==
    static void showStringDemo() {
        System.out.println();
        System.out.println("---- STRING OPERATIONS ----");
        String n = "  asha rao ".trim();
        System.out.println("trim()       : '" + n + "'");
        System.out.println("length()     : " + n.length());
        System.out.println("charAt(0)    : " + n.charAt(0));
        System.out.println("substring    : " + n.substring(0, 4));
        System.out.println("toUpperCase  : " + n.toUpperCase());
        System.out.println("contains rao : " + n.contains("rao"));
        System.out.println("indexOf('r') : " + n.indexOf('r'));

        String a = "Asha";
        String b = new String("Asha");
        System.out.println("a == b            : " + (a == b));                 // false (reference)
        System.out.println("a.equals(b)       : " + a.equals(b));              // true (value)
        System.out.println("equalsIgnoreCase  : " + a.equalsIgnoreCase("ASHA"));

        String line = "Asha,34,118,92,38.6,Y";
        String[] f = line.split(",");
        System.out.println("split() fields    : " + f.length);
        System.out.println("join()            : " + String.join(" | ", f));
    }

    // =====================================================
    //  MODULE 5: FILE I/O  (java.nio.file, try-with-resources)
    // =====================================================
    static String toRecord(Patient p) {
        return String.join(",", p.getName(), String.valueOf(p.getAge()),
                String.valueOf(p.getHeartRate()), String.valueOf(p.getSpo2()),
                String.valueOf(p.getTemp()), p.isConscious() ? "Y" : "N");
    }

    static void saveToFile() {
        List<String> lines = new ArrayList<>();
        for (Patient p : queue) {
            if (!p.isDone()) lines.add(toRecord(p));
        }
        try {
            Files.write(DATA_FILE, lines);            // overwrite with current queue
            System.out.println("Saved " + lines.size() + " patient(s) to " + DATA_FILE.toAbsolutePath());
        } catch (IOException ex) {
            System.out.println("Could not save file: " + ex.getMessage());
        }
    }

    static void appendRecord(Patient p) {
        try {
            Files.writeString(DATA_FILE, toRecord(p) + "\n",
                    StandardOpenOption.APPEND, StandardOpenOption.CREATE);
        } catch (IOException ex) {
            System.out.println("Could not append: " + ex.getMessage());
        }
    }

    // Parse one record line; throws on bad data
    static Patient parseRecord(String line) throws InvalidVitalsException {
        String[] f = line.split(",");
        if (f.length != FIELD_COUNT) {
            throw new InvalidVitalsException("Malformed record (expected " + FIELD_COUNT + " fields)");
        }
        String name = f[0].trim();
        int age = Integer.parseInt(f[1].trim());
        int hr = Integer.parseInt(f[2].trim());
        int spo2 = Integer.parseInt(f[3].trim());
        double temp = Double.parseDouble(f[4].trim());
        boolean conscious = f[5].trim().equalsIgnoreCase("Y");
        return createPatient(name, age, hr, spo2, temp, conscious);
    }

    static void loadFromFile() {
        int loaded = 0, bad = 0;
        // try-with-resources: the reader is closed automatically
        try (BufferedReader br = Files.newBufferedReader(DATA_FILE)) {
            String ln;
            while ((ln = br.readLine()) != null) {
                if (ln.isBlank()) continue;
                try {
                    Patient p = parseRecord(ln);
                    queue.add(p);
                    byId.put(p.getId(), p);
                    loaded++;
                } catch (NumberFormatException | InvalidVitalsException ex) {
                    bad++;                            // bad line never stops the run
                }
            }
            System.out.println("Loaded " + loaded + " patient(s); skipped " + bad + " bad record(s).");
        } catch (IOException ex) {
            System.out.println("No data file found (" + DATA_FILE + "). Save first or load demo data.");
        }
    }

    // =====================================================
    //  DEMO DATA
    // =====================================================
    static void loadDemoData() {
        String[] demo = {
                "Asha,34,118,92,38.6,Y",
                "Ravi,72,142,86,39.8,N",
                "Meena,25,78,98,36.9,Y",
                "Kiran,8,105,95,38.2,Y",
                "Farhan,51,96,97,37.4,Y",
                "Sneha,3,150,88,39.0,Y",
                "bad,record,line"                     // deliberately malformed
        };
        int added = 0, rejected = 0;
        int[] initialWaits = {25, 5, 40, 15, 55, 2, 0};
        for (int i = 0; i < demo.length; i++) {
            try {
                Patient p = parseRecord(demo[i]);
                p.setWait(initialWaits[i]);
                queue.add(p);
                byId.put(p.getId(), p);
                added++;
            } catch (NumberFormatException | InvalidVitalsException ex) {
                rejected++;
            }
        }
        System.out.println("Demo data loaded: " + added + " added, " + rejected + " rejected.");
        showQueue();
    }

    // =====================================================
    //  MENU (while loop) AND MAIN  (MODULE 1)
    // =====================================================
    static void showMenu() {
        System.out.println();
        System.out.println("=========== ER TRIAGE SYSTEM ===========");
        System.out.println(" 1. Register new patient");
        System.out.println(" 2. View waiting queue (priority order)");
        System.out.println(" 3. Call next patient");
        System.out.println(" 4. Search patient by ID");
        System.out.println(" 5. Shift report (streams)");
        System.out.println(" 6. Advance clock (update waiting times)");
        System.out.println(" 7. Save queue to file");
        System.out.println(" 8. Load queue from file");
        System.out.println(" 9. Load demo data");
        System.out.println("10. Array / matrix / string demos");
        System.out.println("11. Remove treated patients");
        System.out.println(" 0. Exit");
        System.out.println("========================================");
    }

    public static void main(String[] args) {
        System.out.println("   HOSPITAL EMERGENCY ROOM TRIAGE SYSTEM  (Team 06)");
        System.out.println("   1 Immediate | 2 Emergent | 3 Urgent | 4 Less Urgent | 5 Non-Urgent");

        int choice = -1;
        while (choice != 0) {                         // main menu repeats until Exit
            showMenu();
            choice = readInt("Enter choice: ", 0, 11);
            switch (choice) {
                case 1:  registerPatient();    break;
                case 2:  showQueue();          break;
                case 3:  callNext();           break;
                case 4:  searchPatient();      break;
                case 5:  showReport();         break;
                case 6:  advanceClock();       break;
                case 7:  saveToFile();         break;
                case 8:  loadFromFile();       break;
                case 9:  loadDemoData();       break;
                case 10:
                    showArrayDemo();
                    showMatrixDemo();
                    showStringDemo();
                    break;
                case 11: removeTreated();      break;
                case 0:
                    System.out.println("Shutting down. Stay safe!");
                    break;
                default:
                    System.out.println("Invalid choice.");
            }
        }
        sc.close();
    }
}

// ---------- MODULE 4: Interface ----------
interface Triageable {
    int calcScore();
}

// ---------- MODULE 4: Custom checked exception ----------
class InvalidVitalsException extends Exception {
    public InvalidVitalsException(String message) {
        super(message);
    }
}

// ---------- MODULE 4: Class, fields, constructors, encapsulation ----------
class Patient implements Triageable, Comparable<Patient> {

    // static members & constants (shared by the whole class)
    static int totalPatients = 0;
    static final int MAX_LEVEL = 5;
    private static int nextId = 101;

    // private fields: access only through methods
    private final int id;
    private String name;
    private int age;
    private int heartRate;
    private int spo2;
    private double temp;
    private boolean conscious;
    private int level;
    private int waitMinutes;
    private boolean done;
    private final Set<String> allergies = new HashSet<>();   // HashSet: no duplicates

    // constructor
    Patient(String name, int age, int heartRate, int spo2, double temp, boolean conscious) {
        this.id = nextId++;
        this.name = name;
        this.age = age;
        this.heartRate = heartRate;
        this.spo2 = spo2;
        this.temp = temp;
        this.conscious = conscious;
        this.level = TriageSystem.levelFromScore(calcScore(), spo2, conscious);
        totalPatients++;
    }

    // overloaded constructor: only a name, everything else default (normal vitals)
    Patient(String name) {
        this(name, 0, 80, 98, 36.8, true);
    }

    // Interface method: score comes from the rules in TriageSystem
    @Override
    public int calcScore() {
        return TriageSystem.calcScore(heartRate, spo2, temp, age);
    }

    // getters
    public int getId()            { return id; }
    public String getName()       { return name; }
    public int getAge()           { return age; }
    public int getHeartRate()     { return heartRate; }
    public int getSpo2()          { return spo2; }
    public double getTemp()       { return temp; }
    public boolean isConscious()  { return conscious; }
    public int getLevel()         { return level; }
    public int getWait()          { return waitMinutes; }
    public boolean isDone()       { return done; }
    public Set<String> getAllergies() { return allergies; }

    // setters with validation (invalid levels are rejected)
    public void setLevel(int level) {
        if (level >= 1 && level <= MAX_LEVEL) {
            this.level = level;
        }
    }
    public void addWait(int minutes) { this.waitMinutes += minutes; }
    public void setWait(int minutes) { this.waitMinutes = Math.max(0, minutes); }
    public void markDone()           { this.done = true; }
    public void addAllergy(String a) { allergies.add(a); }

    static int getTotal() {
        return totalPatients;
    }

    // Comparable: level first (1 is most urgent), then longest wait first
    @Override
    public int compareTo(Patient o) {
        int byLevel = Integer.compare(level, o.level);
        if (byLevel != 0) return byLevel;
        return Integer.compare(o.waitMinutes, waitMinutes);
    }

    @Override
    public String toString() {
        return name + " (L" + level + ")";
    }
}

// ---------- MODULE 4: Inheritance & overriding ----------
class CriticalPatient extends Patient {
    CriticalPatient(String name, int age, int hr, int spo2, double temp, boolean conscious) {
        super(name, age, hr, spo2, temp, conscious);
    }

    @Override
    public String toString() {
        return "URGENT: " + super.toString();
    }
}
