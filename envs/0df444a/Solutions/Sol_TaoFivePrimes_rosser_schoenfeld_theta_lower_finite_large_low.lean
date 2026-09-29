-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_low
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T06:10:42.002928+00:00
-- url     : https://prove2.me/submissions/1fa4392d-f5ef-4a9e-a6e1-1de1ead7be90

import Mathlib

/-! Five Primes: a Rosser-Schoenfeld theta lower bound on a finite range, by a kernel-checked certificate.
* `isPr p` certifies primality of `p < 10201` by one gcd: `gcd p (min (p-1) 100)! = 1`.
* A certificate is a list of checkpoints `c₀ < c₁ < ... ` (the last one `≥ N`); step `i` lists the primes in
  `(cᵢ₋₁, cᵢ]` (checked prime, increasing, in range), so the running product `P` of all listed primes divides
  `primorial cᵢ` (`primorial_add`), and an exponent `aᵢ` with `2 ^ aᵢ ≤ P` gives `aᵢ * log 2 ≤ θ cᵢ`
  (`theta_eq_log_primorial`).
* On `[cᵢ, cᵢ₊₁)` theta is at least `θ cᵢ` while the left side is at most its value at `cᵢ₊₁`, so one integer
  inequality per step (`cond`) suffices; `Real.log_two_gt_d9` turns `aᵢ` into a real bound.
* Everything integer is checked by one `decide +kernel` (plain kernel reduction). -/

set_option autoImplicit false

namespace TFPTheta

open Real

/-- primality certificate for `p < 10201`: no factor `≤ min (p - 1) 100` -/
def isPr (p : ℕ) : Bool :=
  Nat.ble 2 p && Nat.ble p 10200 && Nat.beq (Nat.gcd p (Nat.factorial (min (p - 1) 100))) 1

theorem isPr_prime (p : ℕ) (h : isPr p = true) : p.Prime := by
  simp only [isPr, Bool.and_eq_true] at h
  obtain ⟨⟨h2, hlt⟩, hg⟩ := h
  have h2' := Nat.le_of_ble_eq_true h2
  have hlt' := Nat.le_of_ble_eq_true hlt
  have hg' := Nat.eq_of_beq_eq_true hg
  by_contra hnp
  have hp1 : p ≠ 1 := by omega
  have hmp := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have h2m := hmp.two_le
  have hm100 : p.minFac ≤ 100 := by
    by_contra hc
    have h101 : 101 ≤ p.minFac := by omega
    have hsq' : p.minFac * p.minFac ≤ p := by rw [← pow_two]; exact hsq
    have h3 := le_trans (Nat.mul_le_mul h101 h101) hsq'
    omega
  have hmle : p.minFac ≤ p := Nat.minFac_le (by omega)
  have hmne : p.minFac ≠ p := fun he => hnp (he ▸ hmp)
  have hdf : p.minFac ∣ Nat.factorial (min (p - 1) 100) :=
    Nat.dvd_factorial (by omega) (by omega)
  have hd : p.minFac ∣ Nat.gcd p (Nat.factorial (min (p - 1) 100)) :=
    Nat.dvd_gcd (Nat.minFac_dvd p) hdf
  rw [hg'] at hd
  have := Nat.le_of_dvd one_pos hd
  omega

/-- strictly increasing -/
def incr : List ℕ → Bool
  | a :: b :: l => Nat.blt a b && incr (b :: l)
  | _ => true

theorem incr_pairwise (l : List ℕ) : ∀ a, incr (a :: l) = true → (a :: l).Pairwise (· < ·) := by
  induction l with
  | nil => intro a _; simp
  | cons b l ih =>
    intro a h
    simp only [incr, Bool.and_eq_true] at h
    have hab : a < b := Nat.le_of_ble_eq_true h.1
    have hb := ih b h.2
    refine List.pairwise_cons.2 ⟨?_, hb⟩
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hab
    · exact lt_trans hab ((List.pairwise_cons.1 hb).1 c hc)

/-- the primes of one step: `c :: seg` increasing, entries certified prime and `≤ c'` -/
def segOK (c c' : ℕ) (seg : List ℕ) : Bool :=
  Nat.blt c c' && incr (c :: seg) && seg.all (fun p => isPr p && Nat.ble p c')

theorem segOK_dvd (P c c' : ℕ) (seg : List ℕ) (hP : P ∣ primorial c)
    (h : segOK c c' seg = true) : P * seg.prod ∣ primorial c' := by
  simp only [segOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hcc, hinc⟩, hall⟩ := h
  have hcc' : c < c' := Nat.le_of_ble_eq_true hcc
  have hpw := List.pairwise_cons.1 (incr_pairwise seg c hinc)
  have hnd : seg.Nodup := hpw.2.imp (fun h => ne_of_lt h)
  have hprod : seg.prod = ∏ p ∈ seg.toFinset, p := by
    rw [List.prod_toFinset _ hnd, List.map_id']
  have hadd := primorial_add c (c' - c)
  rw [Nat.add_sub_cancel' hcc'.le] at hadd
  rw [hadd, hprod]
  apply mul_dvd_mul hP
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  rw [List.mem_toFinset] at hp
  have h1 := hpw.1 p hp
  have h2 := hall p hp
  rw [Finset.mem_filter, Finset.mem_Ico]
  exact ⟨⟨by omega, by have := Nat.le_of_ble_eq_true h2.2; omega⟩, isPr_prime p h2.1⟩

theorem theta_ge_of_dvd (P c a : ℕ) (hP : P ∣ primorial c) (h : 2 ^ a ≤ P) :
    (a : ℝ) * log 2 ≤ Chebyshev.theta c := by
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
  have h1 := Nat.le_of_dvd (primorial_pos c) hP
  have h2 : ((2 ^ a : ℕ) : ℝ) ≤ (primorial c : ℝ) := by exact_mod_cast h.trans h1
  rw [← Real.log_pow]
  push_cast at h2
  exact Real.log_le_log (by positivity) h2

/-- the walk: state `(P, c, a)`; each step `(c', a', j', b', seg)` -/
def walk (cond : ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (N : ℕ) :
    ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ × ℕ × List ℕ) → Bool
  | _, c, _, [] => Nat.ble N c
  | P, c, a, (c', a', j, b, seg) :: l =>
      cond c a c' j b && segOK c c' seg && Nat.ble (2 ^ a') (P * seg.prod) &&
        walk cond N (P * seg.prod) c' a' l

theorem walk_sound (cond : ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (N : ℕ) (Q : ℕ → Prop)
    (hcond : ∀ c a c' j b, cond c a c' j b = true → (a : ℝ) * log 2 ≤ Chebyshev.theta c →
      ∀ m, c ≤ m → m < c' → Q m) :
    ∀ (l : List (ℕ × ℕ × ℕ × ℕ × List ℕ)) (P c a : ℕ), walk cond N P c a l = true →
      P ∣ primorial c → 2 ^ a ≤ P → ∀ m, c ≤ m → m < N → Q m := by
  intro l
  induction l with
  | nil =>
    intro P c a h _ _ m h1 h2
    have := Nat.le_of_ble_eq_true h
    omega
  | cons e l ih =>
    obtain ⟨c', a', j, b, seg⟩ := e
    intro P c a h hP ha m h1 h2
    simp only [walk, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hc, hs⟩, hb⟩, hw⟩ := h
    by_cases hm : m < c'
    · exact hcond c a c' j b hc (theta_ge_of_dvd P c a hP ha) m h1 hm
    · exact ih (P * seg.prod) c' a' hw (segOK_dvd P c c' seg hP hs) (Nat.le_of_ble_eq_true hb) m
        (by omega) h2

/-- the whole certificate: the first step lists the primes `≤ c₀` -/
def certB (cond : ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (N c₀ a₀ : ℕ) (seg₀ : List ℕ)
    (l : List (ℕ × ℕ × ℕ × ℕ × List ℕ)) : Bool :=
  segOK 0 c₀ seg₀ && Nat.ble (2 ^ a₀) seg₀.prod && walk cond N seg₀.prod c₀ a₀ l

theorem certB_sound (cond : ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (N : ℕ) (Q : ℕ → Prop)
    (hcond : ∀ c a c' j b, cond c a c' j b = true → (a : ℝ) * log 2 ≤ Chebyshev.theta c →
      ∀ m, c ≤ m → m < c' → Q m)
    (c₀ a₀ : ℕ) (seg₀ : List ℕ) (l : List (ℕ × ℕ × ℕ × ℕ × List ℕ))
    (h : certB cond N c₀ a₀ seg₀ l = true) : ∀ m, c₀ ≤ m → m < N → Q m := by
  simp only [certB, Bool.and_eq_true] at h
  obtain ⟨⟨hs, hb⟩, hw⟩ := h
  have hd := segOK_dvd 1 0 c₀ seg₀ (one_dvd _) hs
  rw [one_mul] at hd
  exact walk_sound cond N Q hcond l seg₀.prod c₀ a₀ hw hd (Nat.le_of_ble_eq_true hb)

theorem lo_le (a : ℕ) : (a : ℝ) * 6931471803 / 10000000000 ≤ a * log 2 := by
  have h := Real.log_two_gt_d9
  norm_num at h
  have ha : (0 : ℝ) ≤ a := by positivity
  nlinarith

/-- step condition for `t - 2 √t < θ t`: `c' - 2 √c' ≤ a * 0.6931471803`, in integers -/
def cond2 (c a c' _j _b : ℕ) : Bool :=
  Nat.ble 1 c &&
    (Nat.ble (c' * 10000000000) (a * 6931471803) ||
      Nat.ble ((c' * 10000000000 - a * 6931471803) ^ 2) (4 * c' * 100000000000000000000))

theorem sqrt_step {t y : ℝ} (ht : 1 ≤ t) (hty : t < y) : t - 2 * √t < y - 2 * √y := by
  have hs : √t < √y := Real.sqrt_lt_sqrt (by linarith) hty
  have h1 : 1 ≤ √t := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_le_sqrt ht
  have et := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ t)
  have ey := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ y)
  nlinarith [mul_pos (sub_pos.2 hs) (by linarith : (0 : ℝ) < √y + √t - 2)]

theorem yA_bound (y a : ℕ)
    (h : (Nat.ble (y * 10000000000) (a * 6931471803) ||
      Nat.ble ((y * 10000000000 - a * 6931471803) ^ 2) (4 * y * 100000000000000000000)) = true) :
    (y : ℝ) - 2 * √(y : ℝ) ≤ a * 6931471803 / 10000000000 := by
  have hs0 : 0 ≤ √(y : ℝ) := Real.sqrt_nonneg _
  have ey := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ y)
  by_cases hc : y * 10000000000 ≤ a * 6931471803
  · have hR : (y : ℝ) * 10000000000 ≤ a * 6931471803 := by exact_mod_cast hc
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  · have hc' : Nat.ble (y * 10000000000) (a * 6931471803) = false := by
      cases hb : Nat.ble (y * 10000000000) (a * 6931471803)
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true hb) hc
    rw [hc', Bool.false_or] at h
    have h' := Nat.le_of_ble_eq_true h
    have hle : a * 6931471803 ≤ y * 10000000000 := by omega
    have hR : (((y * 10000000000 - a * 6931471803) ^ 2 : ℕ) : ℝ) ≤
        ((4 * y * 100000000000000000000 : ℕ) : ℝ) := by exact_mod_cast h'
    push_cast [Nat.cast_sub hle] at hR
    have hpos : (a : ℝ) * 6931471803 ≤ y * 10000000000 := by exact_mod_cast hle
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [sq_nonneg ((y : ℝ) * 10000000000 - a * 6931471803 - 2 * √(y : ℝ) * 10000000000),
      mul_nonneg hs0 (sub_nonneg.2 hpos)]

theorem cond2_sound : ∀ c a c' j b, cond2 c a c' j b = true →
    (a : ℝ) * log 2 ≤ Chebyshev.theta c → ∀ m, c ≤ m → m < c' →
      ∀ t : ℝ, ⌊t⌋₊ = m → 0 ≤ t → t - 2 * √t < Chebyshev.theta t := by
  intro c a c' j b h hθ m hm1 hm2 t ht h0
  simp only [cond2, Bool.and_eq_true] at h
  obtain ⟨h1, h4⟩ := h
  have h1' := Nat.le_of_ble_eq_true h1
  have hmono : Chebyshev.theta c ≤ Chebyshev.theta t := by
    rw [Chebyshev.theta_eq_theta_coe_floor t, ht]
    exact Chebyshev.theta_mono (by exact_mod_cast hm1)
  have htl : (m : ℝ) ≤ t := ht ▸ Nat.floor_le h0
  have htu : t < m + 1 := ht ▸ Nat.lt_floor_add_one t
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast (le_trans h1' hm1)
  have hmv : ((m + 1 : ℕ) : ℝ) ≤ (c' : ℝ) := by exact_mod_cast hm2
  push_cast at hmv
  have hstep := sqrt_step (by linarith : (1 : ℝ) ≤ t) (by linarith : t < (c' : ℝ))
  have hA := yA_bound c' a h4
  have hlo := lo_le a
  linarith

def SEG0 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
   59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
   137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
   227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311,
   313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409,
   419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
   509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613,
   617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719,
   727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827,
   829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941,
   947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049,
   1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163,
   1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283,
   1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423]

def CP : List (ℕ × ℕ × ℕ × ℕ × List ℕ) := [
  (1427, 1962, 0, 0,
    [1427]),
  (1435, 1983, 0, 0,
    [1429, 1433]),
  (1450, 2004, 0, 0,
    [1439, 1447]),
  (1465, 2035, 0, 0,
    [1451, 1453, 1459]),
  (1487, 2077, 0, 0,
    [1471, 1481, 1483, 1487]),
  (1517, 2119, 0, 0,
    [1489, 1493, 1499, 1511]),
  (1547, 2151, 0, 0,
    [1523, 1531, 1543]),
  (1570, 2194, 0, 0,
    [1549, 1553, 1559, 1567]),
  (1600, 2236, 0, 0,
    [1571, 1579, 1583, 1597]),
  (1630, 2311, 0, 0,
    [1601, 1607, 1609, 1613, 1619, 1621, 1627]),
  (1683, 2364, 0, 0,
    [1637, 1657, 1663, 1667, 1669]),
  (1721, 2418, 0, 0,
    [1693, 1697, 1699, 1709, 1721]),
  (1759, 2483, 0, 0,
    [1723, 1733, 1741, 1747, 1753, 1759]),
  (1806, 2537, 0, 0,
    [1777, 1783, 1787, 1789, 1801]),
  (1844, 2569, 0, 0,
    [1811, 1823, 1831]),
  (1867, 2602, 0, 0,
    [1847, 1861, 1867]),
  (1890, 2656, 0, 0,
    [1871, 1873, 1877, 1879, 1889]),
  (1928, 2689, 0, 0,
    [1901, 1907, 1913]),
  (1952, 2732, 0, 0,
    [1931, 1933, 1949, 1951]),
  (1982, 2754, 0, 0,
    [1973, 1979]),
  (1998, 2787, 0, 0,
    [1987, 1993, 1997]),
  (2021, 2831, 0, 0,
    [1999, 2003, 2011, 2017]),
  (2052, 2864, 0, 0,
    [2027, 2029, 2039]),
  (2076, 2897, 0, 0,
    [2053, 2063, 2069]),
  (2099, 2952, 0, 0,
    [2081, 2083, 2087, 2089, 2099]),
  (2138, 3007, 0, 0,
    [2111, 2113, 2129, 2131, 2137]),
  (2177, 3052, 0, 0,
    [2141, 2143, 2153, 2161]),
  (2209, 3085, 0, 0,
    [2179, 2203, 2207]),
  (2232, 3107, 0, 0,
    [2213, 2221]),
  (2248, 3141, 0, 0,
    [2237, 2239, 2243]),
  (2272, 3174, 0, 0,
    [2251, 2267, 2269]),
  (2295, 3219, 0, 0,
    [2273, 2281, 2287, 2293]),
  (2327, 3252, 0, 0,
    [2297, 2309, 2311]),
  (2351, 3308, 0, 0,
    [2333, 2339, 2341, 2347, 2351]),
  (2390, 3375, 0, 0,
    [2357, 2371, 2377, 2381, 2383, 2389]),
  (2438, 3443, 0, 0,
    [2393, 2399, 2411, 2417, 2423, 2437]),
  (2486, 3510, 0, 0,
    [2441, 2447, 2459, 2467, 2473, 2477]),
  (2533, 3544, 0, 0,
    [2503, 2521, 2531]),
  (2557, 3601, 0, 0,
    [2539, 2543, 2549, 2551, 2557]),
  (2597, 3635, 0, 0,
    [2579, 2591, 2593]),
  (2622, 3669, 0, 0,
    [2609, 2617, 2621]),
  (2646, 3680, 0, 0,
    [2633]),
  (2653, 3692, 0, 0,
    [2647]),
  (2662, 3714, 0, 0,
    [2657, 2659]),
  (2677, 3749, 0, 0,
    [2663, 2671, 2677]),
  (2702, 3806, 0, 0,
    [2683, 2687, 2689, 2693, 2699]),
  (2742, 3885, 0, 0,
    [2707, 2711, 2713, 2719, 2729, 2731, 2741]),
  (2798, 3966, 0, 0,
    [2749, 2753, 2767, 2777, 2789, 2791, 2797]),
  (2855, 4046, 0, 0,
    [2801, 2803, 2819, 2833, 2837, 2843, 2851]),
  (2912, 4126, 0, 0,
    [2857, 2861, 2879, 2887, 2897, 2903, 2909]),
  (2968, 4195, 0, 0,
    [2917, 2927, 2939, 2953, 2957, 2963]),
  (3017, 4253, 0, 0,
    [2969, 2971, 2999, 3001, 3011]),
  (3058, 4311, 0, 0,
    [3019, 3023, 3037, 3041, 3049]),
  (3099, 4369, 0, 0,
    [3061, 3067, 3079, 3083, 3089]),
  (3140, 4415, 0, 0,
    [3109, 3119, 3121, 3137]),
  (3172, 4450, 0, 0,
    [3163, 3167, 3169]),
  (3197, 4485, 0, 0,
    [3181, 3187, 3191]),
  (3222, 4532, 0, 0,
    [3203, 3209, 3217, 3221]),
  (3255, 4567, 0, 0,
    [3229, 3251, 3253]),
  (3280, 4602, 0, 0,
    [3257, 3259, 3271]),
  (3304, 4625, 0, 0,
    [3299, 3301]),
  (3321, 4660, 0, 0,
    [3307, 3313, 3319]),
  (3345, 4707, 0, 0,
    [3323, 3329, 3331, 3343]),
  (3378, 4766, 0, 0,
    [3347, 3359, 3361, 3371, 3373]),
  (3420, 4812, 0, 0,
    [3389, 3391, 3407, 3413]),
  (3452, 4836, 0, 0,
    [3433, 3449]),
  (3469, 4895, 0, 0,
    [3457, 3461, 3463, 3467, 3469]),
  (3511, 4930, 0, 0,
    [3491, 3499, 3511]),
  (3536, 4977, 0, 0,
    [3517, 3527, 3529, 3533]),
  (3569, 5036, 0, 0,
    [3539, 3541, 3547, 3557, 3559]),
  (3610, 5095, 0, 0,
    [3571, 3581, 3583, 3593, 3607]),
  (3652, 5166, 0, 0,
    [3613, 3617, 3623, 3631, 3637, 3643]),
  (3702, 5249, 0, 0,
    [3659, 3671, 3673, 3677, 3691, 3697, 3701]),
  (3760, 5308, 0, 0,
    [3709, 3719, 3727, 3733, 3739]),
  (3802, 5380, 0, 0,
    [3761, 3767, 3769, 3779, 3793, 3797]),
  (3853, 5463, 0, 0,
    [3803, 3821, 3823, 3833, 3847, 3851, 3853]),
  (3911, 5535, 0, 0,
    [3863, 3877, 3881, 3889, 3907, 3911]),
  (3962, 5618, 0, 0,
    [3917, 3919, 3923, 3929, 3931, 3943, 3947]),
  (4020, 5702, 0, 0,
    [3967, 3989, 4001, 4003, 4007, 4013, 4019]),
  (4080, 5786, 0, 0,
    [4021, 4027, 4049, 4051, 4057, 4073, 4079]),
  (4139, 5882, 0, 0,
    [4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139]),
  (4206, 5942, 0, 0,
    [4153, 4157, 4159, 4177, 4201]),
  (4249, 6026, 0, 0,
    [4211, 4217, 4219, 4229, 4231, 4241, 4243]),
  (4308, 6123, 0, 0,
    [4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297]),
  (4376, 6207, 0, 0,
    [4327, 4337, 4339, 4349, 4357, 4363, 4373]),
  (4435, 6268, 0, 0,
    [4391, 4397, 4409, 4421, 4423]),
  (4478, 6329, 0, 0,
    [4441, 4447, 4451, 4457, 4463]),
  (4521, 6414, 0, 0,
    [4481, 4483, 4493, 4507, 4513, 4517, 4519]),
  (4581, 6474, 0, 0,
    [4523, 4547, 4549, 4561, 4567]),
  (4623, 6535, 0, 0,
    [4583, 4591, 4597, 4603, 4621]),
  (4666, 6620, 0, 0,
    [4637, 4639, 4643, 4649, 4651, 4657, 4663]),
  (4726, 6694, 0, 0,
    [4673, 4679, 4691, 4703, 4721, 4723]),
  (4778, 6742, 0, 0,
    [4729, 4733, 4751, 4759]),
  (4811, 6816, 0, 0,
    [4783, 4787, 4789, 4793, 4799, 4801]),
  (4863, 6865, 0, 0,
    [4813, 4817, 4831, 4861]),
  (4898, 6901, 0, 0,
    [4871, 4877, 4889]),
  (4923, 6938, 0, 0,
    [4903, 4909, 4919]),
  (4949, 6987, 0, 0,
    [4931, 4933, 4937, 4943]),
  (4984, 7049, 0, 0,
    [4951, 4957, 4967, 4969, 4973]),
  (5027, 7147, 0, 0,
    [4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023]),
  (5096, 7221, 0, 0,
    [5039, 5051, 5059, 5077, 5081, 5087]),
  (5148, 7295, 0, 0,
    [5099, 5101, 5107, 5113, 5119, 5147]),
  (5200, 7369, 0, 0,
    [5153, 5167, 5171, 5179, 5189, 5197]),
  (5252, 7431, 0, 0,
    [5209, 5227, 5231, 5233, 5237]),
  (5296, 7480, 0, 0,
    [5261, 5273, 5279, 5281]),
  (5330, 7530, 0, 0,
    [5297, 5303, 5309, 5323]),
  (5365, 7567, 0, 0,
    [5333, 5347, 5351]),
  (5391, 7591, 0, 0,
    [5381, 5387]),
  (5408, 7629, 0, 0,
    [5393, 5399, 5407]),
  (5435, 7678, 0, 0,
    [5413, 5417, 5419, 5431]),
  (5469, 7728, 0, 0,
    [5437, 5441, 5443, 5449]),
  (5505, 7802, 0, 0,
    [5471, 5477, 5479, 5483, 5501, 5503]),
  (5557, 7877, 0, 0,
    [5507, 5519, 5521, 5527, 5531, 5557]),
  (5609, 7939, 0, 0,
    [5563, 5569, 5573, 5581, 5591]),
  (5653, 8014, 0, 0,
    [5623, 5639, 5641, 5647, 5651, 5653]),
  (5705, 8101, 0, 0,
    [5657, 5659, 5669, 5683, 5689, 5693, 5701]),
  (5767, 8176, 0, 0,
    [5711, 5717, 5737, 5741, 5743, 5749]),
  (5819, 8251, 0, 0,
    [5779, 5783, 5791, 5801, 5807, 5813]),
  (5872, 8376, 0, 0,
    [5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869]),
  (5960, 8477, 0, 0,
    [5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953]),
  (6031, 8539, 0, 0,
    [5981, 5987, 6007, 6011, 6029]),
  (6074, 8615, 0, 0,
    [6037, 6043, 6047, 6053, 6067, 6073]),
  (6128, 8690, 0, 0,
    [6079, 6089, 6091, 6101, 6113, 6121]),
  (6180, 8766, 0, 0,
    [6131, 6133, 6143, 6151, 6163, 6173]),
  (6234, 8854, 0, 0,
    [6197, 6199, 6203, 6211, 6217, 6221, 6229]),
  (6295, 8942, 0, 0,
    [6247, 6257, 6263, 6269, 6271, 6277, 6287]),
  (6357, 9056, 0, 0,
    [6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353]),
  (6437, 9170, 0, 0,
    [6359, 6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427]),
  (6517, 9246, 0, 0,
    [6449, 6451, 6469, 6473, 6481, 6491]),
  (6570, 9334, 0, 0,
    [6521, 6529, 6547, 6551, 6553, 6563, 6569]),
  (6632, 9410, 0, 0,
    [6571, 6577, 6581, 6599, 6607, 6619]),
  (6686, 9487, 0, 0,
    [6637, 6653, 6659, 6661, 6673, 6679]),
  (6740, 9588, 0, 0,
    [6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737]),
  (6810, 9677, 0, 0,
    [6761, 6763, 6779, 6781, 6791, 6793, 6803]),
  (6873, 9792, 0, 0,
    [6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871]),
  (6954, 9881, 0, 0,
    [6883, 6899, 6907, 6911, 6917, 6947, 6949]),
  (7016, 10009, 0, 0,
    [6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997, 7001, 7013]),
  (7106, 10111, 0, 0,
    [7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103]),
  (7177, 10201, 0, 0,
    [7109, 7121, 7127, 7129, 7151, 7159, 7177]),
  (7240, 10304, 0, 0,
    [7187, 7193, 7207, 7211, 7213, 7219, 7229, 7237]),
  (7313, 10393, 0, 0,
    [7243, 7247, 7253, 7283, 7297, 7307, 7309]),
  (7375, 10470, 0, 0,
    [7321, 7331, 7333, 7349, 7351, 7369]),
  (7429, 10509, 0, 0,
    [7393, 7411, 7417]),
  (7456, 10535, 0, 0,
    [7433, 7451]),
  (7475, 10560, 0, 0,
    [7457, 7459]),
  (7492, 10612, 0, 0,
    [7477, 7481, 7487, 7489]),
  (7529, 10676, 0, 0,
    [7499, 7507, 7517, 7523, 7529]),
  (7574, 10766, 0, 0,
    [7537, 7541, 7547, 7549, 7559, 7561, 7573]),
  (7637, 10857, 0, 0,
    [7577, 7583, 7589, 7591, 7603, 7607, 7621]),
  (7701, 10973, 0, 0,
    [7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699]),
  (7782, 11076, 0, 0,
    [7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759]),
  (7854, 11167, 0, 0,
    [7789, 7793, 7817, 7823, 7829, 7841, 7853]),
  (7918, 11257, 0, 0,
    [7867, 7873, 7877, 7879, 7883, 7901, 7907]),
  (7981, 11348, 0, 0,
    [7919, 7927, 7933, 7937, 7949, 7951, 7963]),
  (8045, 11413, 0, 0,
    [7993, 8009, 8011, 8017, 8039]),
  (8090, 11491, 0, 0,
    [8053, 8059, 8069, 8081, 8087, 8089]),
  (8145, 11556, 0, 0,
    [8093, 8101, 8111, 8117, 8123]),
  (8191, 11634, 0, 0,
    [8147, 8161, 8167, 8171, 8179, 8191]),
  (8245, 11725, 0, 0,
    [8209, 8219, 8221, 8231, 8233, 8237, 8243]),
  (8309, 11816, 0, 0,
    [8263, 8269, 8273, 8287, 8291, 8293, 8297]),
  (8373, 11894, 0, 0,
    [8311, 8317, 8329, 8353, 8363, 8369]),
  (8427, 11959, 0, 0,
    [8377, 8387, 8389, 8419, 8423]),
  (8473, 12037, 0, 0,
    [8429, 8431, 8443, 8447, 8461, 8467]),
  (8528, 12090, 0, 0,
    [8501, 8513, 8521, 8527]),
  (8565, 12142, 0, 0,
    [8537, 8539, 8543, 8563]),
  (8601, 12194, 0, 0,
    [8573, 8581, 8597, 8599]),
  (8638, 12246, 0, 0,
    [8609, 8623, 8627, 8629]),
  (8674, 12299, 0, 0,
    [8641, 8647, 8663, 8669]),
  (8711, 12377, 0, 0,
    [8677, 8681, 8689, 8693, 8699, 8707]),
  (8766, 12482, 0, 0,
    [8713, 8719, 8731, 8737, 8741, 8747, 8753, 8761]),
  (8839, 12600, 0, 0,
    [8779, 8783, 8803, 8807, 8819, 8821, 8831, 8837, 8839]),
  (8922, 12679, 0, 0,
    [8849, 8861, 8863, 8867, 8887, 8893]),
  (8977, 12784, 0, 0,
    [8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971]),
  (9051, 12902, 0, 0,
    [8999, 9001, 9007, 9011, 9013, 9029, 9041, 9043, 9049]),
  (9134, 12994, 0, 0,
    [9059, 9067, 9091, 9103, 9109, 9127, 9133]),
  (9198, 13086, 0, 0,
    [9137, 9151, 9157, 9161, 9173, 9181, 9187]),
  (9263, 13191, 0, 0,
    [9199, 9203, 9209, 9221, 9227, 9239, 9241, 9257]),
  (9336, 13284, 0, 0,
    [9277, 9281, 9283, 9293, 9311, 9319, 9323]),
  (9401, 13389, 0, 0,
    [9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397]),
  (9475, 13548, 0, 0,
    [9403, 9413, 9419, 9421, 9431, 9433, 9437, 9439, 9461, 9463, 9467, 9473]),
  (9586, 13667, 0, 0,
    [9479, 9491, 9497, 9511, 9521, 9533, 9539, 9547, 9551]),
  (9669, 13799, 0, 0,
    [9587, 9601, 9613, 9619, 9623, 9629, 9631, 9643, 9649, 9661]),
  (9762, 13931, 0, 0,
    [9677, 9679, 9689, 9697, 9719, 9721, 9733, 9739, 9743, 9749]),
  (9854, 14091, 0, 0,
    [9767, 9769, 9781, 9787, 9791, 9803, 9811, 9817, 9829, 9833, 9839, 9851]),
  (9966, 14250, 0, 0,
    [9857, 9859, 9871, 9883, 9887, 9901, 9907, 9923, 9929, 9931, 9941, 9949]),
  (10001, 0, 0, 0,
    [9967, 9973])]

theorem CERT_ok : certB cond2 10001 1423 1951 SEG0 CP = true := by decide +kernel

end TFPTheta

theorem solution (t : Real) (h1 : 1423 <= t) (h2 : t <= 10 ^ 4) :
    t - 2 * Real.sqrt t < Chebyshev.theta t := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hm1 : 1423 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast h1)
  have hm2 : ⌊t⌋₊ < 10001 := by
    have h := Nat.floor_le ht0
    have h' : (⌊t⌋₊ : ℝ) < 10001 := by norm_num at h2; linarith
    exact_mod_cast h'
  exact TFPTheta.certB_sound TFPTheta.cond2 10001
    (fun m => ∀ t : ℝ, ⌊t⌋₊ = m → 0 ≤ t → t - 2 * √t < Chebyshev.theta t) TFPTheta.cond2_sound
    1423 1951 TFPTheta.SEG0 TFPTheta.CP TFPTheta.CERT_ok ⌊t⌋₊ hm1 hm2 t rfl ht0
