-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_integer_endpoint_certificate_low
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T06:36:43.179291+00:00
-- url     : https://prove2.me/submissions/2fca5efb-87c6-408d-90bf-6848f3e89c9b

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

/-- step condition for `(n+1)(1 - 1/(2 log(n+1))) < θ n`: with `c' ^ j ≤ 2 ^ b` (so
`log c' ≤ (b / j) * 0.6931471808`), require `c' (1 - j / (2 b 0.6931471808)) < a * 0.6931471803` -/
def cond1 (c a c' j b : ℕ) : Bool :=
  Nat.ble 1 c && Nat.ble 1 j && Nat.ble (c' ^ j) (2 ^ b) &&
    Nat.ble (j * 10000000000) (2 * b * 6931471808) &&
    Nat.blt (c' * (2 * b * 6931471808 - j * 10000000000) * 10000000000)
      (a * 6931471803 * (2 * b * 6931471808))

theorem g_mono {s y : ℝ} (hs : 2 ≤ s) (hsy : s ≤ y) :
    s * (1 - 1 / (2 * log s)) ≤ y * (1 - 1 / (2 * log y)) := by
  have hl2 : (1 : ℝ) / 2 < log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this
    linarith
  have hls : log 2 ≤ log s := Real.log_le_log (by norm_num) hs
  have hly : log s ≤ log y := Real.log_le_log (by linarith) hsy
  have h1 : 0 ≤ 1 - 1 / (2 * log s) := by
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  have h2 : 1 - 1 / (2 * log s) ≤ 1 - 1 / (2 * log y) := by
    have : 1 / (2 * log y) ≤ 1 / (2 * log s) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith
  exact mul_le_mul hsy h2 h1 (by linarith)

theorem g_lt (y j b a : ℕ) (hy : 2 ≤ y) (hj : 1 ≤ j) (hyb : y ^ j ≤ 2 ^ b)
    (hjb : j * 10000000000 ≤ 2 * b * 6931471808)
    (hmain : y * (2 * b * 6931471808 - j * 10000000000) * 10000000000 + 1 ≤
      a * 6931471803 * (2 * b * 6931471808)) :
    (y : ℝ) * (1 - 1 / (2 * log y)) < a * 6931471803 / 10000000000 := by
  have hb : 1 ≤ b := by omega
  have hlt2 := Real.log_two_lt_d9
  norm_num at hlt2
  have hyR : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hlogy : 0 < log (y : ℝ) := Real.log_pos (by linarith)
  have h1 : (j : ℝ) * log y ≤ b * log 2 := by
    rw [← Real.log_pow, ← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hyb)
  have hmR : ((y * (2 * b * 6931471808 - j * 10000000000) * 10000000000 + 1 : ℕ) : ℝ) ≤
      ((a * 6931471803 * (2 * b * 6931471808) : ℕ) : ℝ) := by exact_mod_cast hmain
  push_cast [Nat.cast_sub hjb] at hmR
  have hK : (0 : ℝ) < 2 * b * 6931471808 := by positivity
  have hq : (j : ℝ) * 10000000000 / (2 * b * 6931471808) < 1 / (2 * log y) := by
    rw [div_lt_div_iff₀ hK (by positivity)]
    nlinarith
  have hstep : (y : ℝ) * (1 - 1 / (2 * log y)) <
      y * (1 - j * 10000000000 / (2 * b * 6931471808)) := by
    have hy0 : (0 : ℝ) < y := by linarith
    nlinarith
  have hstep2 : (y : ℝ) * (1 - j * 10000000000 / (2 * b * 6931471808)) <
      a * 6931471803 / 10000000000 := by
    have e : (y : ℝ) * (1 - j * 10000000000 / (2 * b * 6931471808)) =
        y * (2 * b * 6931471808 - j * 10000000000) / (2 * b * 6931471808) := by
      field_simp
    rw [e, div_lt_div_iff₀ hK (by norm_num)]
    linarith
  linarith

theorem cond1_sound : ∀ c a c' j b, cond1 c a c' j b = true →
    (a : ℝ) * log 2 ≤ Chebyshev.theta c → ∀ m, c ≤ m → m < c' →
      ((m : ℝ) + 1) * (1 - 1 / (2 * log ((m : ℝ) + 1))) < Chebyshev.theta m := by
  intro c a c' j b h hθ m hm1 hm2
  simp only [cond1, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have h1' := Nat.le_of_ble_eq_true h1
  have hmono : Chebyshev.theta c ≤ Chebyshev.theta m :=
    Chebyshev.theta_mono (by exact_mod_cast hm1)
  have hm2R : ((m + 1 : ℕ) : ℝ) ≤ (c' : ℝ) := by exact_mod_cast hm2
  have hm1R : ((2 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ m + 1)
  push_cast at hm2R hm1R
  have hg := g_mono hm1R hm2R
  have hlt := g_lt c' j b a (by omega) (Nat.le_of_ble_eq_true h2) (Nat.le_of_ble_eq_true h3)
    (Nat.le_of_ble_eq_true h4) (Nat.le_of_ble_eq_true h5)
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
   1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409]

def CP : List (ℕ × ℕ × ℕ × ℕ × List ℕ) := [
  (1444, 1993, 2, 21,
    [1423, 1427, 1429, 1433, 1439]),
  (1482, 2056, 5, 53,
    [1447, 1451, 1453, 1459, 1471, 1481]),
  (1529, 2130, 5, 53,
    [1483, 1487, 1489, 1493, 1499, 1511, 1523]),
  (1583, 2226, 3, 32,
    [1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583]),
  (1654, 2321, 7, 75,
    [1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637]),
  (1724, 2429, 9, 97,
    [1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723]),
  (1803, 2537, 6, 65,
    [1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801]),
  (1883, 2645, 9, 98,
    [1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879]),
  (1962, 2732, 1, 11,
    [1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951]),
  (2026, 2831, 1, 11,
    [1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017]),
  (2099, 2952, 14, 155,
    [2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099]),
  (2188, 3063, 8, 89,
    [2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179]),
  (2269, 3174, 5, 56,
    [2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269]),
  (2351, 3308, 5, 56,
    [2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351]),
  (2449, 3465, 7, 79,
    [2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447]),
  (2565, 3601, 3, 34,
    [2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557]),
  (2664, 3726, 5, 57,
    [2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663]),
  (2756, 3908, 7, 80,
    [2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753]),
  (2890, 4092, 2, 23,
    [2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887]),
  (3025, 4276, 23, 266,
    [2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023]),
  (3159, 4415, 3, 35,
    [3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137]),
  (3261, 4590, 7, 82,
    [3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259]),
  (3390, 4777, 11, 129,
    [3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389]),
  (3527, 4954, 14, 165,
    [3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527]),
  (3656, 5166, 7, 83,
    [3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631,
     3637, 3643]),
  (3811, 5392, 10, 119,
    [3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779,
     3793, 3797, 3803]),
  (3977, 5630, 24, 287,
    [3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929,
     3931, 3943, 3947, 3967]),
  (4151, 5882, 22, 265,
    [3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099,
     4111, 4127, 4129, 4133, 4139]),
  (4335, 6135, 9, 109,
    [4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271,
     4273, 4283, 4289, 4297, 4327]),
  (4521, 6414, 7, 85,
    [4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463,
     4481, 4483, 4493, 4507, 4513, 4517, 4519]),
  (4725, 6694, 24, 293,
    [4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657,
     4663, 4673, 4679, 4691, 4703, 4721, 4723]),
  (4929, 6938, 7, 86,
    [4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877,
     4889, 4903, 4909, 4919]),
  (5108, 7258, 25, 308,
    [4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021,
     5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107]),
  (5342, 7542, 13, 161,
    [5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273,
     5279, 5281, 5297, 5303, 5309, 5323, 5333]),
  (5549, 7865, 9, 112,
    [5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471,
     5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531]),
  (5785, 8201, 2, 25,
    [5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683,
     5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783]),
  (6030, 8539, 7, 88,
    [5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881,
     5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987, 6007, 6011, 6029]),
  (6277, 8930, 8, 101,
    [6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151,
     6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277]),
  (6563, 9322, 19, 241,
    [6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389,
     6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563]),
  (6849, 9741, 4, 51,
    [6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701,
     6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833,
     6841]),
  (7154, 10175, 6, 77,
    [6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977,
     6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127,
     7129, 7151]),
  (7471, 10560, 8, 103,
    [7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307,
     7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451, 7457, 7459]),
  (7752, 11037, 13, 168,
    [7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573,
     7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699,
     7703, 7717, 7723, 7727, 7741]),
  (8099, 11504, 1, 13,
    [7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901,
     7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009, 8011, 8017, 8039, 8053, 8059, 8069,
     8081, 8087, 8089, 8093]),
  (8440, 11985, 16, 209,
    [8101, 8111, 8117, 8123, 8147, 8161, 8167, 8171, 8179, 8191, 8209, 8219, 8221, 8231, 8233, 8237,
     8243, 8263, 8269, 8273, 8287, 8291, 8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387,
     8389, 8419, 8423, 8429, 8431]),
  (8791, 12508, 9, 118,
    [8443, 8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 8581, 8597, 8599,
     8609, 8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677, 8681, 8689, 8693, 8699, 8707, 8713, 8719,
     8731, 8737, 8741, 8747, 8753, 8761, 8779, 8783]),
  (9172, 13047, 6, 79,
    [8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849, 8861, 8863, 8867, 8887, 8893, 8923, 8929, 8933,
     8941, 8951, 8963, 8969, 8971, 8999, 9001, 9007, 9011, 9013, 9029, 9041, 9043, 9049, 9059, 9067,
     9091, 9103, 9109, 9127, 9133, 9137, 9151, 9157, 9161]),
  (9565, 13667, 22, 291,
    [9173, 9181, 9187, 9199, 9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293, 9311,
     9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397, 9403, 9413, 9419, 9421, 9431, 9433,
     9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491, 9497, 9511, 9521, 9533, 9539, 9547, 9551]),
  (10001, 0, 2, 27,
    [9587, 9601, 9613, 9619, 9623, 9629, 9631, 9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721,
     9733, 9739, 9743, 9749, 9767, 9769, 9781, 9787, 9791, 9803, 9811, 9817, 9829, 9833, 9839, 9851,
     9857, 9859, 9871, 9883, 9887, 9901, 9907, 9923, 9929, 9931, 9941, 9949, 9967, 9973])]

theorem CERT_ok : certB cond1 10001 1420 1941 SEG0 CP = true := by decide +kernel

end TFPTheta

theorem solution (n : Nat) (h1 : 1420 <= n) (h2 : n <= 10000) :
    ((n : Real) + 1) * (1 - 1 / (2 * Real.log ((n : Real) + 1))) < Chebyshev.theta n := by
  exact TFPTheta.certB_sound TFPTheta.cond1 10001
    (fun m => ((m : ℝ) + 1) * (1 - 1 / (2 * Real.log ((m : ℝ) + 1))) < Chebyshev.theta m)
    TFPTheta.cond1_sound 1420 1941 TFPTheta.SEG0 TFPTheta.CP TFPTheta.CERT_ok n h1 (by omega)
