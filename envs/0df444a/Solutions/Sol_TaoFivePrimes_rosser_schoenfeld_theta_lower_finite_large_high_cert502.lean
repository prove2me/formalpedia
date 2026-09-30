-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert502
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T00:20:05.707525+00:00
-- url     : https://prove2.me/submissions/ac30539d-16e6-40d6-8599-66e353031938

import Mathlib

/-! Five Primes: `(n + 1) - 2 √(n + 1) ≤ θ n` on `[98961910, 99999999]` and `Cb / 2 ^ 40 ≤ θ 100000000`, by a kernel-checked
segment certificate on top of the hypothesis `θ 98961910 ≥ C / 2 ^ 40`.
* `θ c = log c#`. With `Y = 98961910#`, the walk keeps `m * 2 ^ e * Y ≤ c#` (a 128-bit mantissa `m`),
  so `θ c ≥ C / 2 ^ 40 + (e + 127) log 2`; the kernel never evaluates `Y`.
* Each step codes the primes of `(c, c']` as base-16 gap digits of one number `G` (digit `d < 15` is a
  gap `2 d + 2`, digit `15` skips 28), multiplies them in, and proves them all prime by one
  `gcd (product) 10000! = 1` (valid below `10001 ^ 2 > 10 ^ 8`).
* One integer inequality per step (`stepOK`) covers `[c, c')` since `θ` is monotone and
  `y - 2 √y` increases; the end constant uses `2 ^ bb ≤ m ^ j` and `Real.log_two_gt_d9`.
* All integer work is one `decide +kernel` (plain kernel reduction, no `native_decide`). -/

set_option autoImplicit false

namespace TFPTheta5

/-- `10000!`: every prime below `10 ^ 4` divides it, so it is the factor pool of the primality test -/
def F : ℕ := Nat.factorial 10000

theorem F_eq : F = Nat.factorial 10000 := rfl

/-- a number in `[2, 10 ^ 8]` coprime to `10000!` is prime (`10 ^ 8 < 10001 ^ 2`) -/
theorem prime_of_coprime (q : ℕ) (h2 : 2 ≤ q) (hq : q ≤ 100000000) (hc : Nat.gcd q F = 1) :
    q.Prime := by
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmp := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hsq' : q.minFac * q.minFac ≤ q := by rw [← pow_two]; exact hsq
  have h10 : q.minFac ≤ 10000 := by
    by_contra hc'
    have h1 : 10001 ≤ q.minFac := by omega
    have h3 := le_trans (Nat.mul_le_mul h1 h1) hsq'
    omega
  have hdF : q.minFac ∣ F := by
    rw [F_eq]
    exact Nat.dvd_factorial hmp.pos h10
  have hd : q.minFac ∣ Nat.gcd q F := Nat.dvd_gcd (Nat.minFac_dvd q) hdF
  rw [hc] at hd
  have := Nat.le_of_dvd one_pos hd
  have := hmp.two_le
  omega

/-- `dec acc p G k` decodes the base-16 digits of `G` (low digit first; the leading `1` ends the
list): digit `d < 15` is a prime `q = p + 2 d + 2`, multiplied into `acc`; digit `15` only moves the
position `p` by `28`. It returns the product and the last position (`k` is fuel; product `0` on
running out of fuel). Primality is not tested here: the walk tests the whole product at once. -/
def dec (acc p G : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, p)
  | k + 1 =>
    cond (Nat.ble G 1) (acc, p)
      (cond (Nat.beq (Nat.mod G 16) 15) (dec acc (Nat.add p 28) (Nat.div G 16) k)
        (let q := Nat.add p (Nat.add (Nat.mul 2 (Nat.mod G 16)) 2)
         let a := Nat.mul acc q
         cond (Nat.beq a 0) (0, p) (dec a q (Nat.div G 16) k)))

theorem dec_mono : ∀ (k acc p G : ℕ), p ≤ (dec acc p G k).2 := by
  intro k
  induction k with
  | zero => intro acc p G; simp [dec]
  | succ k ih =>
    intro acc p G
    simp only [dec]
    cases h1 : Nat.ble G 1
    · simp only [cond_false]
      cases h2 : Nat.beq (Nat.mod G 16) 15
      · simp only [cond_false]
        cases h3 : Nat.beq (Nat.mul acc (Nat.add p (Nat.add (Nat.mul 2 (Nat.mod G 16)) 2))) 0
        · simp only [cond_false]
          have := ih (Nat.mul acc (Nat.add p (Nat.add (Nat.mul 2 (Nat.mod G 16)) 2)))
            (Nat.add p (Nat.add (Nat.mul 2 (Nat.mod G 16)) 2)) (Nat.div G 16)
          have e : Nat.add p (Nat.add (Nat.mul 2 (Nat.mod G 16)) 2) = p + (2 * (G % 16) + 2) := rfl
          omega
        · simp
      · simp only [cond_true]
        have := ih acc (Nat.add p 28) (Nat.div G 16)
        have e : Nat.add p 28 = p + 28 := rfl
        omega
    · simp

theorem dec_dvd : ∀ (k acc p G : ℕ), acc ∣ (dec acc p G k).1 := by
  intro k
  induction k with
  | zero => intro acc p G; simp [dec]
  | succ k ih =>
    intro acc p G
    simp only [dec]
    cases h1 : Nat.ble G 1
    · simp only [cond_false]
      cases h2 : Nat.beq (Nat.mod G 16) 15
      · simp only [cond_false]
        cases h3 : Nat.beq (Nat.mul acc (Nat.add p (Nat.add (Nat.mul 2 (Nat.mod G 16)) 2))) 0
        · simp only [cond_false]
          exact dvd_trans (Dvd.intro _ rfl) (ih _ _ _)
        · simp
      · simp only [cond_true]
        exact ih _ _ _
    · simp

theorem primorial_succ_prime (n : ℕ) (h : (n + 1).Prime) :
    primorial (n + 1) = (n + 1) * primorial n := by
  unfold primorial
  rw [Finset.range_add_one, Finset.filter_insert, if_pos h, Finset.prod_insert]
  simp

theorem primorial_le_of_prime (p q : ℕ) (hpq : p < q) (hq : q.Prime) :
    q * primorial p ≤ primorial q := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  rw [primorial_succ_prime r hq]
  exact Nat.mul_le_mul_left _ (primorial_mono (by omega))

/-- the abstract-`Y` invariant: `acc * Y ≤ p#` survives decoding, provided the final product is
coprime to `10000!` and the final position is at most `10 ^ 8` -/
theorem dec_le (Y : ℕ) : ∀ (k acc p G : ℕ), acc * Y ≤ primorial p →
    Nat.gcd (dec acc p G k).1 F = 1 → (dec acc p G k).2 ≤ 100000000 →
    (dec acc p G k).1 * Y ≤ primorial (dec acc p G k).2 := by
  intro k
  induction k with
  | zero => intro acc p G _ _ _; simp [dec]
  | succ k ih =>
    intro acc p G h hc hr
    simp only [dec] at hc hr ⊢
    cases h1 : Nat.ble G 1
    · simp only [h1, cond_false] at hc hr ⊢
      cases h2 : Nat.beq (Nat.mod G 16) 15
      · simp only [h2, cond_false] at hc hr ⊢
        set q := Nat.add p (Nat.add (Nat.mul 2 (Nat.mod G 16)) 2) with hqdef
        have hq : q = p + (2 * (G % 16) + 2) := rfl
        cases h3 : Nat.beq (Nat.mul acc q) 0
        · simp only [h3, cond_false] at hc hr ⊢
          have hmono := dec_mono k (Nat.mul acc q) q (Nat.div G 16)
          have hqd : q ∣ (dec (Nat.mul acc q) q (Nat.div G 16) k).1 :=
            dvd_trans (Dvd.intro_left _ rfl) (dec_dvd k _ q _)
          have hcq : Nat.gcd q F = 1 := Nat.Coprime.coprime_dvd_left hqd hc
          have hprime : q.Prime := prime_of_coprime q (by omega) (by omega) hcq
          apply ih _ q _ _ hc hr
          have hpq := primorial_le_of_prime p q (by omega) hprime
          show acc * q * Y ≤ primorial q
          calc acc * q * Y = q * (acc * Y) := by ring
            _ ≤ q * primorial p := Nat.mul_le_mul_left _ h
            _ ≤ primorial q := hpq
        · simp only [h3, cond_true] at hc hr ⊢
          simp
      · simp only [h2, cond_true] at hc hr ⊢
        apply ih _ _ _ _ hc hr
        exact le_trans h (primorial_mono (Nat.le_add_right p 28))
    · simpa [h1] using h

/-- the lower bound on `log₂ (m * 2 ^ e)` used by a step: `e + 127` once the mantissa is full -/
def bits (m e : ℕ) : ℕ := cond (Nat.ble (2 ^ 127) m) (e + 127) e

theorem bits_le (m e : ℕ) (hm : 1 ≤ m) : 2 ^ bits m e ≤ m * 2 ^ e := by
  unfold bits
  cases h : Nat.ble (2 ^ 127) m
  · simp only [cond_false]
    exact le_mul_of_one_le_left (by positivity) hm
  · simp only [cond_true]
    rw [pow_add, mul_comm (2 ^ e)]
    exact Nat.mul_le_mul_right _ (Nat.le_of_ble_eq_true h)

/-- shifting right by `s` and scaling by `2 ^ s` loses nothing on the upper bound -/
theorem shift_le (q e s P : ℕ) (h : q * 2 ^ e ≤ P) : Nat.shiftRight q s * 2 ^ (e + s) ≤ P := by
  have hsr : Nat.shiftRight q s = q / 2 ^ s := Nat.shiftRight_eq_div_pow _ _
  rw [hsr, pow_add]
  calc q / 2 ^ s * (2 ^ e * 2 ^ s) = (q / 2 ^ s * 2 ^ s) * 2 ^ e := by ring
    _ ≤ q * 2 ^ e := Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
    _ ≤ P := h

theorem shift_leY (q e s Y P : ℕ) (h : q * 2 ^ e * Y ≤ P) :
    Nat.shiftRight q s * 2 ^ (e + s) * Y ≤ P := by
  have hsr : Nat.shiftRight q s = q / 2 ^ s := Nat.shiftRight_eq_div_pow _ _
  rw [hsr, pow_add]
  calc q / 2 ^ s * (2 ^ e * 2 ^ s) * Y = (q / 2 ^ s * 2 ^ s) * 2 ^ e * Y := by ring
    _ ≤ q * 2 ^ e * Y := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _))
    _ ≤ P := h

/-- step condition: `c' - 2 √c' ≤ C / 2 ^ 40 + A * 0.6931471803`, cleared of denominators
(`K = 10 ^ 10 * 2 ^ 40`) -/
def stepOK (C c A c' : ℕ) : Bool :=
  Nat.ble 1 c &&
    (Nat.ble (c' * 10995116277760000000000) (C * 10000000000 + A * 7621233844999975600128) ||
      Nat.ble ((c' * 10995116277760000000000 - (C * 10000000000 + A * 7621233844999975600128)) ^ 2)
        (c' * 483570327845851669882470400000000000000000000))

/-- final condition: `2 ^ bb ≤ m ^ j` and `Cb / 2 ^ 40 ≤ C / 2 ^ 40 + (bb + e j) / j * 0.6931471803` -/
def finOK (C Cb m e j bb : ℕ) : Bool :=
  Nat.ble 1 j && Nat.ble (2 ^ bb) (m ^ j) &&
    Nat.ble (Cb * j * 10000000000) (C * j * 10000000000 + (bb + e * j) * 7621233844999975600128)

/-- the walk: state `(m, c, e)` with `m * 2 ^ e * Y ≤ c#`; a step `(de, G)` decodes the primes of
`(c, c']` from `G`, tests them all by one gcd with `10000!`, multiplies them into `m` and drops `de`
bits; the end covers `[c, N)` and checks the constant at `N` -/
def walk (C N Cb j bb : ℕ) : ℕ → ℕ → ℕ → List (ℕ × ℕ) → Bool
  | m, c, e, [] => Nat.ble 1 m && Nat.ble c N && stepOK C c (bits m e) N && finOK C Cb m e j bb
  | m, c, e, (de, G) :: l =>
      let sr := dec 1 c G 100000
      Nat.ble 1 m && stepOK C c (bits m e) sr.2 && Nat.beq (Nat.gcd sr.1 F) 1 &&
        Nat.ble sr.2 100000000 &&
        walk C N Cb j bb (Nat.shiftRight (Nat.mul m sr.1) de) sr.2 (e + de) l

theorem lo_le (a : ℕ) : (a : ℝ) * 6931471803 / 10000000000 ≤ a * Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num at h
  have ha : (0 : ℝ) ≤ a := by positivity
  nlinarith

theorem log_lb (C Y c m e : ℕ) (hY : (C : ℝ) / 2 ^ 40 ≤ Real.log Y) (hY0 : 0 < Y) (hm : 1 ≤ m)
    (h : m * 2 ^ e * Y ≤ primorial c) :
    (C : ℝ) / 2 ^ 40 + bits m e * Real.log 2 ≤ Chebyshev.theta (c : ℝ) := by
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
  have h2 : 2 ^ bits m e * Y ≤ primorial c :=
    le_trans (Nat.mul_le_mul_right _ (bits_le m e hm)) h
  have h2' : ((2 ^ bits m e * Y : ℕ) : ℝ) ≤ (primorial c : ℝ) := by exact_mod_cast h2
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY0
  push_cast at h2'
  have hl := Real.log_le_log (by positivity) h2'
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hl
  linarith

theorem sqrt_mono {t y : ℝ} (ht : 1 ≤ t) (hty : t ≤ y) : t - 2 * √t ≤ y - 2 * √y := by
  have hs : √t ≤ √y := Real.sqrt_le_sqrt hty
  have h1 : 1 ≤ √t := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_le_sqrt ht
  have et := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ t)
  have ey := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ y)
  nlinarith [mul_nonneg (sub_nonneg.2 hs) (by linarith : (0 : ℝ) ≤ √y + √t - 2)]

theorem yZ_bound (y Z : ℕ)
    (h : (Nat.ble (y * 10995116277760000000000) Z ||
      Nat.ble ((y * 10995116277760000000000 - Z) ^ 2)
        (y * 483570327845851669882470400000000000000000000)) = true) :
    (y : ℝ) - 2 * √(y : ℝ) ≤ Z / 10995116277760000000000 := by
  have hs0 : 0 ≤ √(y : ℝ) := Real.sqrt_nonneg _
  have ey := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ y)
  by_cases hc : y * 10995116277760000000000 ≤ Z
  · have hR : (y : ℝ) * 10995116277760000000000 ≤ Z := by exact_mod_cast hc
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  · have hc' : Nat.ble (y * 10995116277760000000000) Z = false := by
      cases hb : Nat.ble (y * 10995116277760000000000) Z
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true hb) hc
    rw [hc', Bool.false_or] at h
    have h' := Nat.le_of_ble_eq_true h
    have hle : Z ≤ y * 10995116277760000000000 := by omega
    have hR : (((y * 10995116277760000000000 - Z) ^ 2 : ℕ) : ℝ) ≤
        ((y * 483570327845851669882470400000000000000000000 : ℕ) : ℝ) := by exact_mod_cast h'
    push_cast [Nat.cast_sub hle] at hR
    have hpos : (Z : ℝ) ≤ y * 10995116277760000000000 := by exact_mod_cast hle
    rw [le_div_iff₀ (by norm_num)]
    by_contra hneg
    rw [not_le] at hneg
    have hA : 0 ≤ 2 * √(y : ℝ) * 10995116277760000000000 := by positivity
    have hB : 2 * √(y : ℝ) * 10995116277760000000000 < (y : ℝ) * 10995116277760000000000 - Z := by
      linarith
    have := mul_self_lt_mul_self hA hB
    nlinarith

theorem stepOK_sound (C c A c' : ℕ) (h : stepOK C c A c' = true)
    (hθ : (C : ℝ) / 2 ^ 40 + A * Real.log 2 ≤ Chebyshev.theta (c : ℝ)) :
    ∀ n : ℕ, c ≤ n → n < c' →
      ((n : ℝ) + 1) - 2 * √((n : ℝ) + 1) ≤ Chebyshev.theta (n : ℝ) := by
  intro n hn1 hn2
  simp only [stepOK, Bool.and_eq_true] at h
  obtain ⟨h1, h4⟩ := h
  have h1' := Nat.le_of_ble_eq_true h1
  have hmono : Chebyshev.theta (c : ℝ) ≤ Chebyshev.theta (n : ℝ) :=
    Chebyshev.theta_mono (by exact_mod_cast hn1)
  have hnR : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := by positivity
    linarith
  have hnc : (n : ℝ) + 1 ≤ (c' : ℝ) := by
    have : n + 1 ≤ c' := hn2
    exact_mod_cast this
  have hstep := sqrt_mono hnR hnc
  have hZ := yZ_bound c' _ h4
  have hZ' : (((C * 10000000000 + A * 7621233844999975600128 : ℕ) : ℝ)) / 10995116277760000000000 =
      (C : ℝ) / 2 ^ 40 + A * 6931471803 / 10000000000 := by
    push_cast
    ring
  have hlo := lo_le A
  linarith

theorem finOK_sound (C Cb m e j bb Y N : ℕ) (h : finOK C Cb m e j bb = true)
    (hY : (C : ℝ) / 2 ^ 40 ≤ Real.log Y) (hY0 : 0 < Y) (hm : 1 ≤ m)
    (hP : m * 2 ^ e * Y ≤ primorial N) :
    (Cb : ℝ) / 2 ^ 40 ≤ Chebyshev.theta (N : ℝ) := by
  simp only [finOK, Bool.and_eq_true] at h
  obtain ⟨⟨hj, hb⟩, hc⟩ := h
  have hj' := Nat.le_of_ble_eq_true hj
  have hb' := Nat.le_of_ble_eq_true hb
  have hc' := Nat.le_of_ble_eq_true hc
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY0
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj'
  have hPR : ((m * 2 ^ e * Y : ℕ) : ℝ) ≤ (primorial N : ℝ) := by exact_mod_cast hP
  push_cast at hPR
  have hl := Real.log_le_log (by positivity) hPR
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow] at hl
  -- `bb * log 2 ≤ j * log m`
  have hbR : ((2 ^ bb : ℕ) : ℝ) ≤ ((m ^ j : ℕ) : ℝ) := by exact_mod_cast hb'
  push_cast at hbR
  have hl2 := Real.log_le_log (by positivity) hbR
  rw [Real.log_pow, Real.log_pow] at hl2
  have hcR : ((Cb * j * 10000000000 : ℕ) : ℝ) ≤
      ((C * j * 10000000000 + (bb + e * j) * 7621233844999975600128 : ℕ) : ℝ) := by
    exact_mod_cast hc'
  push_cast at hcR
  have hlo := lo_le (bb + e * j)
  push_cast at hlo
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- combine: j * (Cb / 2^40) ≤ j * (C / 2^40) + (bb + e j) log 2 ≤ j * θ N
  have key : (j : ℝ) * ((Cb : ℝ) / 2 ^ 40) ≤ (j : ℝ) * ((C : ℝ) / 2 ^ 40) + (bb + e * j) * Real.log 2 := by
    have e1 : (j : ℝ) * ((Cb : ℝ) / 2 ^ 40) = (Cb * j * 10000000000 : ℝ) / 10995116277760000000000 := by
      ring
    have e2 : (j : ℝ) * ((C : ℝ) / 2 ^ 40) + (bb + e * j) * 6931471803 / 10000000000 =
        (C * j * 10000000000 + (bb + e * j) * 7621233844999975600128 : ℝ) / 10995116277760000000000 := by
      ring
    have e3 : (Cb * j * 10000000000 : ℝ) / 10995116277760000000000 ≤
        (C * j * 10000000000 + (bb + e * j) * 7621233844999975600128 : ℝ) / 10995116277760000000000 :=
      div_le_div_of_nonneg_right hcR (by norm_num)
    linarith
  have key2 : (j : ℝ) * ((C : ℝ) / 2 ^ 40) + (bb + e * j) * Real.log 2 ≤
      (j : ℝ) * Real.log (primorial N : ℝ) := by
    nlinarith
  have := le_of_mul_le_mul_left (le_trans key key2) hjR
  exact this

theorem walk_sound (C N Cb j bb Y : ℕ) (hY : (C : ℝ) / 2 ^ 40 ≤ Real.log Y) (hY0 : 0 < Y) :
    ∀ (l : List (ℕ × ℕ)) (m c e : ℕ), walk C N Cb j bb m c e l = true →
      m * 2 ^ e * Y ≤ primorial c →
      (∀ n : ℕ, c ≤ n → n < N →
        ((n : ℝ) + 1) - 2 * √((n : ℝ) + 1) ≤ Chebyshev.theta (n : ℝ)) ∧
        (Cb : ℝ) / 2 ^ 40 ≤ Chebyshev.theta (N : ℝ) := by
  intro l
  induction l with
  | nil =>
    intro m c e h hP
    simp only [walk, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hm, hcN⟩, hs⟩, hf⟩ := h
    have hm' := Nat.le_of_ble_eq_true hm
    have hcN' := Nat.le_of_ble_eq_true hcN
    refine ⟨stepOK_sound C c _ N hs (log_lb C Y c m e hY hY0 hm' hP), ?_⟩
    exact finOK_sound C Cb m e j bb Y N hf hY hY0 hm' (le_trans hP (primorial_mono hcN'))
  | cons st l ih =>
    obtain ⟨de, G⟩ := st
    intro m c e h hP
    simp only [walk, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hm, hs⟩, hg⟩, hr⟩, hw⟩ := h
    have hm' := Nat.le_of_ble_eq_true hm
    have hg' := Nat.eq_of_beq_eq_true hg
    have hr' := Nat.le_of_ble_eq_true hr
    have hθ := log_lb C Y c m e hY hY0 hm' hP
    have hcov := stepOK_sound C c _ _ hs hθ
    have hd := dec_le (m * 2 ^ e * Y) 100000 1 c G (by rw [one_mul]; exact hP) hg' hr'
    have hd' : Nat.mul m (dec 1 c G 100000).1 * 2 ^ e * Y ≤ primorial (dec 1 c G 100000).2 := by
      show m * (dec 1 c G 100000).1 * 2 ^ e * Y ≤ _
      calc m * (dec 1 c G 100000).1 * 2 ^ e * Y = (dec 1 c G 100000).1 * (m * 2 ^ e * Y) := by ring
        _ ≤ _ := hd
    have hs'' := shift_leY (Nat.mul m (dec 1 c G 100000).1) e de Y _ hd'
    have hmono := dec_mono 100000 1 c G
    obtain ⟨ih1, ih2⟩ := ih _ _ _ hw hs''
    refine ⟨fun n hn1 hn2 => ?_, ih2⟩
    by_cases hn : n < (dec 1 c G 100000).2
    · exact hcov n hn1 hn
    · exact ih1 n (by omega) hn2

/-- the leaf form: from `C / 2 ^ 40 ≤ θ a` and `a# ≤ c₀#`, a passing walk from `(1, c₀, 0)` gives the
bound on `[c₀, N)` and the constant at `N` -/
theorem leaf (C Cb a c₀ N j bb : ℕ) (l : List (ℕ × ℕ)) (h : walk C N Cb j bb 1 c₀ 0 l = true)
    (hc₀ : primorial a ≤ primorial c₀) (hbase : (C : ℝ) / 2 ^ 40 ≤ Chebyshev.theta (a : ℝ)) :
    (∀ n : ℕ, c₀ ≤ n → n < N →
      ((n : ℝ) + 1) - 2 * √((n : ℝ) + 1) ≤ Chebyshev.theta (n : ℝ)) ∧
      (Cb : ℝ) / 2 ^ 40 ≤ Chebyshev.theta (N : ℝ) := by
  have hY : (C : ℝ) / 2 ^ 40 ≤ Real.log (primorial a : ℕ) := by
    rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast] at hbase
    exact hbase
  exact walk_sound C N Cb j bb (primorial a) hY (primorial_pos a) l 1 c₀ 0 h
    (by rw [one_mul, pow_zero, one_mul]; exact hc₀)

/-- an even start `n + 1` has the same primorial as `n` -/
theorem primorial_even (n : ℕ) (h1 : n ≠ 1) (hn : n % 2 = 1) : primorial (n + 1) ≤ primorial n :=
  le_of_eq (primorial_succ h1 (Nat.odd_iff.mpr hn))


def CP0 : List (ℕ × ℕ) :=
  [(9381, 0x16211fd3dfffc1319cf219215be29f649f81f6f5fdf55f501294831b05f0a2085426f022e1ff493f5422803fcf8fe3122ff5eefb4f45ff5845e2b2af2b8f2502d291592f3bf352a3f551f2f01b682f4f4c73d67856d07536f72642c41ff9aca829167af5ef6e24dff312529726f016d6ee10eb732d922e4cf62e2889f516408cf85493f1e92a913f806ffaf40768456f88556a81ff645e61029f211fb480156f5382fc5ab96f8764b4f4b65e9fb25a26a85b052131fff4ff28958bd6feff55d053f123b5f3fc26f4e9889ff3d6d21f1e61295fe94b5232824950),
   (10146, 0x1910552162192731aff04850480123bf61313d50156128957958b762fbffe513a82af2191cbd32d2ff7504ffeb85420a237610bab2957b538191e9a31e0211ff2b82536ff5341f8198f05256f2126f31e1f1c3f5489b485e888b8916108f6b2f0246f56eb2735f59462f02f1f131ff3f2e8f35bf3432cf7eb5346544f4852e082750ed6fff163f246b14f6f8d28852e2cb2f0b10bf3daf1cbd670d642e3213fe2ecf322f5cb752055f04c1c1b0133f55fbc41fbf622a201354ec526ff0a3818981012323f1550761b2c484ffc1b070de64645bffb16227917f512625402f),
   (9801, 0x11b3f0b7b9792f836f7ff12ff6ff5256f4f16120d6751f85ea4f2122b25fff58af43e4eb255c156182fffe54f84534653f4042c21b68f532762a1f2a016f0a3515b976f5b08557c124f46f64292a3e2f975e53d80a015645ff41f2f6570aca2642228cdaf54dff929f22f83210ee454f8b521804324082216a9191cef861553585a29f6f952a4f1ca6f27f766f198f6cf759bfffa379168819faf1370163f4af9fa379210a31effef9274f7381b02f20e5106fde981202f61344f6fd0851359ff1f2a34af40d688b53ff922ee18c13b4370487fd6763ff01295e7013f5df7e),
   (9774, 0x1462810156d6f32a0cff67e853d59d8622be1359feb7552535f052f580d6aff2f62f0b15354ff1323f1595228f82df5e515bc1624324017f22f56701ff24ec2a04207cd0285cf1550105d4fe41fa855234954356f2246a86eab63f6fa2b0b1385f5afe19f38105fe1ff9be2163f7262db1fb1314f8ef05d0a9ba07226f34b256f6762464ff1ffd21f13855e7afd92f02ac49a55b2ec54e1f2f7f221bff25f295848595f501cd54f51507e29888b2726875864580732108a91ffcf483aaf40796f57b4f54ff6f3f8f322492a228082793f5f5e839ff39fb74f21236f),
   (9801, 0x13f4982a3121fef65420eaca535428c5f3f5c1314f76a202459f6dee58521f16e4e641f42670527ffa21fa82c74fe228a0a64b318016f8295f4f22f56ecfa8223f984971ff801b0b212ff433ff070d36fbf2b94ce55bfc5d0a613f9a616524525b263f13aeb1fdc4ff4085f1f76f6cf2708aaf4dfb517f8461b58010a808a20a22322de02d2bffed4f5f3a31955f2313f686f485043bf623f12b2946214f4ce3f9f5124f57340d046fe340452324264ff524b208b432f3f3249dff22450d20be105f07621ff7295e79279f643f045882e67943f34baf5438e6f52e),
   (10173, 0x182083f6ff2898f654379875674f4b1f8fb61227f55bf39fa0e44ff8040bf36f3fd3f28e5b235d2372c521084319ef35242c52126512b5e50d3e435b214f431655f6192f0b4c22fb0bf9e2e2d988248251f519e7b049faf14f11ff26e2a954327912328f234e56f1f84250d52c2a86462fc729e45c2e2f2b913d0bde9420525a9ed06f254317f10e10810b514fa6a04804e012af2eef6d89221ff49b2f2bc75226e465843b763f5756b8f26708f2c408524e045e3183a566ff51f22bea8cf347f282872b22af16bfb32121f5f87ff5c3f162216705fbb01b67ec2522f1ffff),
   (10439, 0x19461626fbf344f2254021255e2b827fe7550423226f9f5d085f04c426513582a68f6b464224f2a0a826213d081358f0d045ff15ec492f9b271fa20852b459b519d5bb2eaf2f22e36f8e5b5a02138d59f01286aff2f26f3fc2123bf0d3555e3f128670d291b2082823fd23fc461ff2fff15058fe6e2f0551be31ec8ba37509ff55af436f77ff916581c5a81fa2558c1952d681676a8643edb010d2322e5f3ac40818265afff3545562f0b101e24f52fc123f87f88bf0d9f24fe24e55e84f4cd0d6f20d86e510eaafa2529543581945bcf93fe283f2825a27f5f204b35f38217f54375b256f),
   (10624, 0x1321b3b43762288b16493f225a27ff34053f45e83429f01977f108f82df8e2783f26255fe25b8c15c164ff8f31205f1f4e022f2059f242629f8bd1f11f1323f1b52022706f47fa8047f7b9252424f210d3d92b10d3f5318bb5623ff26281853cf26fe76de50840b5578ff8a8b982e3f10d9734bff8183f225df5f68a3f62a04344f3f7057584f27646cf435d3a6f53704615688f27f28a2616525d03fa6211ffb56493f450461ff4b348643f085524ff4202735f6f9461355feff3f4646f0549f20d053f4505462129fff4506f7341ff6812e3b438270d6123841ff7f3f816f23e52f7f156108f054b058431c1c52f3d),
   (10625, 0x1224fb8b1553e8b846f98a2b95dc55a351239ffcb423ae622a010b18ffaeb0491ff49fc462f255837cf0162f3a31fff96f4024ecede20b214ff344ffaff3dcb77f156729407502243f32f9f81f5ed31044ffcf254ff7f7047f432a0818ff4261079db85c46d9b28b2103f57ce150855f5c2f208bd20402276f0213d7fe8cffb92f6f82285263f855f64234553f054970126f8027af28a8553b485c6f73f65b7b2e3cf51e5501b04325bb14f18010d28c5a223792426750489d4f4c3f4862281ff8be1af21652183fe012501c822f3f25ff8b13f3d6439fcf12ff2f65f2287fa3a2918222340a6f3ef6bb22b1025f),
   (10624, 0x113221014f6f704e387c16a03f21269ff65f06ff06f10163f849570d6d3f2c1202ba20224235166ff21ff9f4ff012e3468ac1cb72b1ff04506ffec583ff251fb4562d7f23fe2f6f6f949f8951b2ff41f22cf6f5f51f425318ff21ec44f8434641f2522e8a65f24f5f26434eb26be2156f51ff4f420b15052f6ae640526ff05f50434c2216a6254ee0d311ff2822024508fb042314f43b89f6fdff8e42262f07502d085d5501af2b287c192d59462f35767594ee310792f4f21202f3543a9f32f6540401293f1ff9fa4f2f079f658241f1202429ef868221ff42089f543426b7b0b15916f02cf51e92736ff68545ff6f43d0e40758),
   (10625, 0x11ce1975e6f2081261672b64c5e5f0525bfaf84532725084c12b0e876813f502405703f46fe53f01342292161228c2464646f99ff07643e5f0a264ff1c44f1268192138f018805731c1042bcb1507e0404ff13f06f255454f21e9d6f7ff250cf72e0255a34e3124fba93f5543f62ef641f74fa6bcff8b226154f762211f4828c722ff3f43f616f24f1526429a2927bee32789f64203f586f6f758ff123ab592faf21e820408a2b526852b216721f2a4f4959fe73255f8ff3f82b5a07055f2617f7921504855322cf55e5fdf5459213570a6f34ff73489fec13f820164c2821e50219f8913d1fae92a61e0),
   (10624, 0x1d33f1045853128b294c157fd3b2e82f1f433f3f4349e2bfb26731010a3f59f5024562463fb25f07291c4bec2f50512dff918684df76242cfe3d894af51cd0d3f2504258313f9211f552f91029fe3f2be15bdf5a25087e68184f43cf40105452023f8f3243e854ff22ef5867942e26b135755864347ff5ff26f52bd3287046ba07641f4622aff5f0a22948532401c14ff4f1df4533fe1586f8265f23434671fd823f0d043b2fb898183a32e2164af4e505257b0844fa58591043a5254f5db592b2540e5f6b2183b6fe852f9131cd02f67ff8405570759842c8124ff4f8403f13d919adfa93f1011f435),
   (10625, 0x1492f33f21e595f856f381e3f0126f20a583437c55738f9750d012370e126f01ffe2846f6f0124ff321234c4298f3122235dff219f20a8e5c729431011fd3f8313bf21fa3459f21f5abcf83276f22af2f622cf5fc2192f53e22185af12bc2433f9ff6f0703f45bc17f2f3f6f946fdf11fd0737835f9f50a2e36ff94df252289f1e6eb70452292f6a23aafbf31eff7ff214ff01cb76109f464c126215623ff06f22e11f522d010bf6f2312ff8f5016f05e2525132735166ff86f2ff156e150a95f23be81979bf92aeb33febe8ea02464c125ff42622572321e4f584952b42cd1fbcf42af19a622542e22e6162a4f4e6f5026f47ff3f0),
   (10625, 0x111ff32ae02783f1ff0d6f021c18805218022f3fb0425c5f626ff236f24376126e510b43d37808252f251fd01c2d7f7ffb1ff28a64bffa31e5af219d02f92f942653fe811f282f3432d4f6f431677fa626f23f464b27f53fa04df1373fb1f437253f4ffbc4612af1c5f65d2e531ff549b3f81927984924b27fd6429eed7f4049f20544f1b558324ffe1b0528f94c1bffba509ff95813ac40481f5e3fb1671f1b6485ff54508f0a38a3d505b4507040423f910811f759f343f897ff8793f7b8348c75223f6b785621644f19fbff51054868d505fff45e01653f85133f6ff09f24b2b0123b2464202f2027640525bf96f49cfb54c),
   (10624, 0x19f5ca9434055255126229f4c12295f3726429d65f3542081855948af8a01653ff23e2b22795f4fcf76408427f8f3f359f3f45e59841ff051fff5e62f32f9ef93fae9873f914f84e8550e782345286f8b0dff5126150575205210b27682b8183575cf21f254e9b165fc42384616d05eb2f3f04351205f3f927501238821531e852923fa4fcf1ff3fa2cb5a3db1f2d9422625e7550b51372e258952155ff492a7f2d92d6f20cff943f5925191651e3fe6b8e58d57f4804e31ff72b927522825e53558e3f22f625a94523ba8ce732101507223e8f822aff9a38f6f9a2ff1b32fff126fafa911f57551f84c15c),
   (10625, 0x161806f5f3a35fff5e2f92a2ff8841f49cff1ff62f3b4235467e5af48086f843454fee6ff6a92164b3d0a03f45c8f6a0701207e2345322b15e9ef22258af2fca976a235efaf2167b533f2256f2d055282fcb8e43458dfd2014f22d86fc2d58ce21b0423725319872ff5f0a2025f62bd08f0b4205f0cf4ffcf3fba3242863f43f25297b1fb2128be9241f182e298daf19105210cf12af4df1e654b92d3549faf5795d28970b2f29d3a20183f580ae6f95fb94649795fb292e765f256fb1f4022780cf46423fe9f23f02246e3f7954c2750e13fc84c43729eb549543453f9548284fa079a21fa3f0821082f0821),
   (10625, 0x12d0ae3a3a353f14ffbff7cb1c1b2262f205e27c5a6211f2fb9211f5a852e59f0512b59180efc45af5d324c480daf103f48b83243e81325450b14f813fc165151f24265a5ff1b1f84621e04cfb8057cf9197b6db4f40d92181f751f3f14f1e3dcf80cf8fec5454fd31016251b9ba27ff22b1ff51f40d56e1af40158ff765f35d016f5254f6f13812584fa6b7b92f3b9fab1f1235a1f12ff2fc55f0e43d6b247f4df4ee2bb2235bf85c1c2f3fff1e265f6ac1253e452cb584e95fbc3f8d8b010a2221f5b73432fbcb10481ff970b2f62450213fe671fa85561021643f33f13d0d6211f16754f11f7e4f7cd531070a),
   (10625, 0x11503f1aff4f3fbb215838422024cf073762b513f610e5a3210701ff71f6ffb27f16a910a1f8f32f9f6f1f24054e2af436f2f20a65b2570405f2ff485c16a91af165f0dff24916bf38b28e5546fb2238fe62f3ed50272cfafd2e2ff5f6249572321268d2e64580a1fd4f1e33fa624e0a25563f12612df825a3a9f321b08e4bff3f464262a054916706f5f88c4677f46403f4040436ff259ae52cf68f921235a5641f1928187f2d976132f6727f2d053f15619e71fe12310d8866f841f29f7615e6494041f7951ca532b55fe38432fff404e643a92cf8d6f93f15c192467075684312529b542508ef3e1088f2232),
   (10625, 0x1ef346ef2502a53fb1fd3d7f5e1649221b03f12b3d4fbf502f6f6e4ff4502f6f3157f8f2319db84ff0198f616a9fe98165b462126cf8f0402135427fd6191c2488502f9a313f6a68f322753f973857e22fff341ff0244f4503fbf685ef082518021b94c85782e2682513d0227649f4ff23756fca08813d082b1070708765a949adf12b250b15c525a8e0516f9ac5b755b62fff723d04ffa3e512b9f9276156513a29f0ef5041fb3f44fabcfc11f27ff44f15ff6f5f7f5f053f7cb8a262a92dff3f1ce7cfb084025a6fff6ff2e8ff480d3405521947f122c194c4072ff18359f1324672914ffc13d61589b4ff55f053fdc3ff94eb0),
   (10625, 0x1073a65f5ff2a08437dfeb24670d5019a8013f68229fd6e281209fbe22f09fe2a345851fa62f523a61c1af186b41f549857504af25f5043a3db4f85576ee5f5c58b1e651c79194ff82e22f2e61236f1b6f3a94821f1c8a04312bff2f20512ff1ff85a3f0e2f6198f0546fcb25405f91233f5456f919274fba39f6f48bcd23f05f2922b2f5372625aff44f4c7086fbf8084ff5a076e2f0585f8b2640e4261efffffe192512345866f4978627b4ff34561c2102f235a259b1503f287624eff70d62f651c2f6d6494b9b2540577f218927c1389f21640d4ff1f489e1349f6ffff7f55724f26f816fc5f052fb3b4e8e2263ff9e40),
   (10625, 0x156f5678855618e042cd1f7522e3d95ed92f834b6123f34e0b19702fc585f04ff3f1ebff5f234954af8228817fbf3a6750735455af48eca324821f48b1f15856e3ffc2f6726ab3d33f1ecfc2103ff27f252a322f06f2405f6fff13813f085a02f23f8b3844ff32b43165cf10d3f345ff5a3d08bde58532152027627084be624fff0daf16f6549521851fb541f1ff570ea3d32d8327041f12351238f95f082fe01b3a01015ff756d5328fe3222459f0bf612976a0846755323fb14ff6f52dfd2223787ff25c22ed6213f92eb13166f1df13f081673fb622401ff213ea348c1b99f49f084922a94253a4f192a040245),
   (10625, 0x110d235fe2ff77fb2f3fe7ff0d054e381b262f8e7ff8945df279b215ff21250a35b512621e911f9fa7f2d08552a03f11f2f26556fd2cd56b79726d56ae538ba646afff6240524ff282e2f63f2464c844fa7ff36f284567316f27f85f2fff3ebf27ff4fa7ff087cfc1265f0705f0e2b21af12640459a6e51327cd3f3a62ef21ff7ff022b102f1f57ff16f3401b297501ff85b468874f544f545ff273bf84f846ac1bff1657558c5a015586857592512624084520a0affd3a05ef2c3ff014f6f2402213fce572c49542c71f73f62cf10b514f727f29f44ff0aaf845348bec1ca53f64ff7612c3f5a34e6f1ff36fd2c2f2853e211f12b56bba28),
   (10625, 0x18af403f2f0150a6762fff54b20d311f213f642327894cf01df86f432450d6127f2d1f102f2b8ca0255579f1fb1b5ff4e6f5612ff7021209f41f810d5cb83f7922fc570854642e05f043f8b01ffdc5a5b95f6f3276ba643e48045343f08e24bbe4fd2345e99fa3f340a8804625d865f3f2c6f57595afff0221e534af13a35f9f232b41ff91ff8bf3fb208b25548cf6e7646f52224fa1faaffc2e73124ff3d51f8224235f6279fc18b67df5421f4327052ee552a3e4853a82b9783a38a0bfaff86b242b25c3fe1b0b1804565a52024b6fe7f401cf225af2219a68f35fc43e2137ffd33f7054c11ff916d801b2672cf26f1f),
   (10625, 0x182fff01cfc21646d34648378349486fbbff2fc3f8135f0858a29e103f523f42fffff521521ff62194afba6d26881e8af13fe5521ff553e816405512911f85812223a3a9a04e2b34592810d31232f85221ff3f8651c4826857047f5f345b3f21fd62523f48022f6fff40855f4f581ff45802f684efff2985a295f055213212b02b19b272084e3101cf0cf40b79f50223f571f46753161c8fee2356faffd6221288082f3d3cf76f0529f152801edf2fe3f5266f12925d1f5462ba7ff253a50b51af41ff3512258501b20d641f434525cefff7ff4280d5982843f3f86f21ff9828d4f15c1b0cf461862dcb4c23ff610ba6795f0a8),
   (10625, 0x1ee594535d03f27e4f784f489b58f040be12049e54352129e5f505d07cf20a9f2c2452651b222057bc5f521ff292b4eb6f05e841ff523462cf5848531b927053f573fb64c2240703ffc495e3f5d642954985f081eece467232b70e1610733fb6fa071f221af4973a5ff76aee20796f810d0216211f1ffcff6f64940125ff45bb23a3843288f1f491b1f45e0124f81655765b10d5979a35e2e3fe1cb10461529bf0165b5e5792153465434ce2d89a20407be0e16255578b010bf0d4f43516123f3e54831ffdb3cf71f25845327079b224be2370a206fd022f3f0ea9a915e5025a37ff42),
   (10626, 0x105e46fb54f8f2e35b1645b018df45985e1b06f405fcf6273fcf2b323f2d56f357c11ffe24fd502d280ef23fcf6210d0423212ce3ff2864886f9138496f213194e6bf641ff6b7ff10b12627353ff9d03f551297af52216d0d314ff058480486ab1f41f3f288b462f0ef3bf3f92f5264321208726d855cf01cbd21ff26131c6f8189582a310b12df732d5286f619a4f12c5f203f738192f561b04c18028192e47ff3a5af3f11f42054651b68e840b71f81b02f232b22d2ffd62122b64087ff71f79e40453a57fffff0525a3f554f274f3fa53a04375e36f18082cf7016a046f9f0493ff043467e688109f2b26f5f6bbaeb),
   (10625, 0x16258b15e66ff36f857b67827f2b40d1ff20d2b0b5f61011fd0189f0704072b53228e13162d09faff581af15676b3f25f1f2b423faff9fe50ed0e8452bb7fd0d342b535a35d0a9d263f4649483a63ff052e5f2e35cf183540225fb2c1b95f7ff64622e5a33fa0404344f8cf83ff801b0b6ffc3fb8846f2ce2d0575b92a2564262b2821be3ee5ea3a2bcd0b248c1504ca827f44ff258086f7537bc76709f1611f2b1b0dff19f67040753f27f73819731af4079f088fc5723cffe3e259f249f9218081b51f22467e853ace5f0bfcf0cf28b4ff120434b3bef0b28246f5083fa645fff8c761223a918316b24c1),
   (10625, 0x1c841f4c1bff7628a054ff4e92f3425554f2404679f2bff2f04bc5fe316fcf1ffb0159f0139f5db61ca36f82b5a253129247f8f619f522e673fe61552297644f23f8d0a9163f2f6f20210e9f4ffea52effd0283f4205884b83a5cf0a345c2192fe35f68549496ff985d20a8b655722801613ed22534806f22759f3e76223ff82e5040432541f3fb7e627ce2f943f04df18341f138b2f0dfff59101ff13276548ffe872822322f92559f46f1ff294df104612289e105f6b4354c6fb43498a34558292f54ff802f88053fed0d0d2351c2452263f1ff854354b6f8082fff16f67235cff04af2f6e9f5e4384b925fc4323f750882f2),
   (10625, 0x1657bc1372233f83f7b05f8c1b31ffd67e01caaffcf32284079fff1af51917ffe53161c734268571f165f927328452ecf3481f21943f2805f3f8ff1b2b1f162a378344f6ff0de93f86f4e892a310156421f432fcb8525bf322d05f2612346fb6f9f1f85a32feb237c43f80b19ab4f584e313ffff2e1f512911f1df1c52108f1f5282f53f0d4f46f5201e38ebf2280e87c19132f267b80216b52feb4f840a226ae2fff31cbace16e3f8a20e5f20527aff1f12614f162f0e2dcf2c7b9d9242bb880baff759a0d5678387820b105d6f2509f11ff3bf32a311ff20584e856165494888b3f54f104c5f8ff25f5021b69fef3f9e29f557),
   (10626, 0x19f273a9572c85f946f081e62b4670d684b25269f814f452e046159855215b24f58214fb19a0724f5be13431087eb805b103fa5327e9d92bf62d019708e18253a9134833f165781f435f6aff5fe3423213e12675af2a913ab5945046bf8915cfb35fb649e55222d62242647f18eaf2f291eff6f43f5504261942232825fc82134610a9a3fe4f229fe2f3fe3f4f2186f0245384af1356f10bf31286526f84b6102b2403f1c51cd92241ff0884623f2d3f852052f09f2b211ff22b7f5fb2652551652459f81ff3f6224b3f376a2ff403f1b50816180766f4928e45854fe157f76543b6f1cf047f22ef0b1),
   (10625, 0x194232105fb8ff1ffd8b8941fbf641f1321580d043e3fa4f12238bd8612b50547f1ffa1f9f810cfe73526ff32424f8f36f2b104051562f7f5826f1ff481f1ffb1648b913fb0e5407e322f01e3f3b3f2fe32f9f3e5a6e101e7f5105ef4f5f6251cbf4f495a3f67e7f245385f6e43a4f49f0d019f292704ff4af2f2052b3f122c126168fbc23ffc2461b02f62134bc194aff4f14f256ff61c70549d2fffaf8821ff1e658722589ef684804559b22ac45580510d2cdb8afb43f3138b71feea26fb3216f3f806f3f104b53405f64989f16121ff02f3243f84f40e855756f2984056f8f4f11f8456b702fe613815b5342bc7643f1fe72ff1b6f610),
   (10626, 0x12153e17ff2684927203fe5dc2495fb982457f1ce8222a39f5f0b2a94348ff4321074f2f3e53f21282564e3521ca2ff105f559fc134023fe731ffe7b67ff1294910164041f7e0db1fb55de822310b76216f9bf22e7f23f2f263f8a629f73242b05e9fb21eaf10d28df1c46573225e22ed21fd55ec4af7c5819f593f9f11f1534e9e22f8ff4074f4c78b38e4c1c4255838429b5f0451f45ff5d98f6226ffc1208d54fcfd34e64070765f5cf0b257e281ff1f4b506fd835fe91df497c1e2052fe01250840d9753a62404262b3f23f14f8575054233f8de61b8afe528faff53214ff92e2f29f3fe082b1084e864bb2),
   (10625, 0x125086f2a34057226f025f021ff1c1385b7b258679a1f17fa32422531b95ea0d257fd94537565f625f2597084b251fe8f675322cf8a654325f352d57f1c42af43a9adf1385f084e7f49451ff9d03fb735f671f1385f54fa2e01c1236ff533f1282940b11f5483e41f841f451f823f465f5856467352a6f6e10ee1ff25e7b6f322f07918262a021250723a8ff1c51be0dc282f3f50d50be14f58f2981ffd86d08fb9421fe83fba68d040b223ff38f06f45bee08a6b43f262543fff7328f9f532b136fa9f6fcee47fd4fd9b4520aca56ebf0e3fe4018df402f20e2519f596ff6186e2d220521ca0e4ec1345cb1cb),
   (10413, 0x148e02f3f6f1f73225f9a801ffd53e56ffc780d9f6b5f507ccf14ff0e810d57fb5257c219164ff6f49fb2502587325527254fd5b262f012345319fdffb5671f52b8d520183f04520e849e40a382281af2180aff1262435fc855f382fca382f57f74f407b2058ab01642c139f55e3f137e9a1f457fbf64343f04556fff2b576f1f3fa343cfa93fb2f581f55be2f0b41fd599fe2885d9b46ae1f44ffb089ffafbf95f918205f868f5041f7914f2e4c9f5dff5a2c4202b45268f0511fd05a62fc408243bf8015503fd3f25e013f2374f754f5d235123431dff9ae6e2462f014f855fff73e22fe0858d3737cb21e044f7cf56f),
   (10227, 0x182a54f5219a328f342cf01014ff07e26219e2d385199f546152b852e8e5507054236f14fe841fdb3a3aca250bf62f3f67e65cf40a3e137e62a9acb6ffff22180d31653ffe8346f1f1042ffa2315266ffb049bcf2d38a52651043ab6bd8229f06ff5921536f2543434ff3f47f75e56a322fff2fb2503f13f01eafd0b22161206f524526702f99fdaf55245ee4f84642048293fe812af52f9f85af5b10e87229812df213fb202212ce5f05f36f5881baf79fec2f01b4ff0ed93f12c1672809f284e97c101261c19ab83a1f2a3deb079f50d6f0e6ff646ef670a257ffbff1b9213f2b96f4670a92),
   (10281, 0x12e31c159e84354268825f261b804028104232f31ec6f51916f89e227aff1fa22613405b28a2e05e3f55216a805f3154f2409f9ff34c4649a252672344f1250106f841ff5c24286ea204e832efff4652b1262ba53812292854643401bdfdff85a3f32f1f79f0b47f43fe81f4204ff12013256ff5074fa54ffb017f4ff2f922255e8729f01b223f38f91910241ff35f0554b262494c467e6f4f48e2c407edfb24e7f1bff6f46a9bf35211ff57f5dff738fcf5314ff2343e852f23a626f3f21e0eef51f9ff2925f862103fbf1f213e5b42922fb50e5f88564919a9120213458586f29457f2ef268f8349406f),
   (10439, 0x1b2df7ff58258229f2159552f2204c5545c406f24341f469f27208a0853fa56a34565f85613ef232423fb673485c5486fb23b2e6f4085402a085d02e1643f911f572208191288052f05f0d552afe5f07cb5f951df54520ac1ff1262a09f2734832d9726cf42925f8294223135f04529161982f62f86f028eab3243fe3d8b538f643d95f237cf89f596ff7f15e073fcf6841f5b12640422ff5b2701ff2728013497292a23f3fb65b731e2c825faf22819a3f50d4ff8fff06f126a8cf31ee6e19a27f213d7f824cb56fa25ff11f762a0108b41f8840ed05d2262cf5d65e12323f21ffe48ffb6f843f83a6f),
   (10520, 0x1085d538a223f052a347fba55673762185df9ff928216a3e884df4976d07e35f651670486a208fb57f23ff97822323f12285b21f48985bf23f32735e2f0123e5f0a864644ff32b52fb56ea6241f723fb4ff3a352f89251c8ae6d017fbf5ff4e38bf625241f8cf6ff5e3e8f62104263f13d6ee2bf4f5425022e16f054c8120a222864357ff9f43efb9a921910a316408bd3badf4610ed2e231837b92f4f5f021022f89f0d6b7231df181f2555f296f8fff43b4618314f1384084531e6274fa8041ff5265731c7b58e2677f5e19b1010570459f8af23fa0734ff1238124fb5f59f296f46f01ffe8f676705b43f),
   (10387, 0x1026f85f0d06ff5ff5f9285d3f52ffe705579dbe021857f25f324cf3f0db36f2b2545317fa1ff040eb14f163ff805b76127f2211fb74f228b213fc3f162467ff1af17f2ba928b8a3453fdf4b0461ff2d50d4f40b4268f8b3192f01205192f316b6f4341ff9edcf33f40e41f5fc7b56243450a3ef3401857f1e31e262e16549fc12afde95b5a1f4e26b4ff10e137ce8f94048e51ffe9840d9198d63f6f42b33ff80884857f104580acac40164643f6211ffff2f0165d3129a226215535f32ba65f32216bf6464ff154ff0510b1af5a352735f208efff5b19a35b15ff13d0213f08274f55d6101b50a372888266fa),
   (10254, 0x1883f2f0d3f28594b9f0437c8d9a524f1c12921595f3fffa20a204e2586215ff12b34341fd31075c4ff10d9284834ff16435efcf8cbf615822081e4f7caff9fdff156731049246b154fef04805b216f0d0cff33f5e4e31dfba6228a0a92fe68f6f02243f5316a6f23fb6845832845678dfb4021b5aff3f3571f7b03f134387b59d98f3e70bf8612833ff3f3546240ac8b4313a3e42288589f0162750d87fe84313f044fbf0d22c58f1f45ffb81673f04316b84826ae0de057982f251f25e5f4f12644f5bf2b62f02a1ff267044f541fd36fb4ee6b426a640e450d06ff21f2bdb67e3212652f0b7),
   (10174, 0x18540d4fa3b11f49ac15236f41f223ff50ae81f25f6b1838f83581802a520ef3b3f225fe3b8f0d052b426aff1235f94e5b62cf7646d0227b8862db922b13551280827e67944f402bf5253d7f2a62194328fff183f561558862a3545346b42ff189571ff02a62fdf852a2040a2cf37581f5d61b5c57fff1f7e373213d5688f2208fb297342c420a924801ff436f2f2b6e7afd52be61aff085f686fbb6ff2bdf2b77f2f861ff1643402466f75806ff8612cd08e1e56e547fba55835ef7f44f44f8131640a87ff3faf49194df2fe29cf4073101fff53f31e043a62429d23f02b528242629f1599f),
   (9563, 0x14ca61b85808825f36f78ff429f56d08fb2af1b97bec1235d209f23fa26f5381c4921223277ff3f2325de02fafd3f53b6f462d52b3f829cf2f0753e192165f502a671fbf6126f0e44fd2b7f701943f50b1229f010485075027cf6a646f0e44fe1324641f4ffb1b251f53f1852bcf66f7e67536f25e5f525e3a1f26f5e72dfbf984058a8851f1b53f51f2cffff6fbf012ff165f68a20a8b65d1f6fef03f2128c2b12cf0843f62a87f5d0828faf763f402a91237ec5bf27f75046a07553d534280dff2b21c2d93f43de025cfe2d0545fff551fe483f6f07586526fd09f5),
   (9670, 0x136f3f53ff267fff1ff3f61c4b92218c13f1f5763f2e47f40be1927586f2585534501df7b61c22a8bb263f10d56241f6fd3d24f2784f6f546b3f242804cf3ac52fff408a61345c4ec8f04016409f273f042c24af812b3f0a07070d223102a08f2fff33ff3fffe19fff27370cf1e508126254c5eac242372621371f57b850465f0ebf340e24af210a4f8275256f5e33f4223ab36f243192180a35248556f640e1c162f6f83f672208d67c123f6195edb04b23526f27ecb16f586b42b9128ffd9aff13aeec494232a1f52a29e41fe134e025d92fff1b045e2c26f),
   (9165, 0x12f92fe3189fcfe38126101cd51f85e5e1af7aff0b13f62ab4fae65b5fbbffbfbe94204e0e43f3cf2b43e1252654dff7f7583f831c1becd04c19d5203f4559f5895f3a6f8e92f6733f3f78b6fb53b49434024cf23f262ed22e7f87e642655f25e0b5e83f1923fa6f26870b705f02f24f2783498195f4f52275e591af75ff24b042e5c43fb2925e4e8af17f14fa08546733f243fb2504df81205f8e282ccf76a50840734954aff5312b1f128593f17f540bfaf9fe4025f5229ef27f84081679fff7232704ff221898164237df7945c6fbf),
   (9032, 0x19ba8b292493f132405408fb654952bf59e215208f06f2a53eace21fffe08763f15c405f3f235f3ea355436f49d591052154f4349404565f91895f61537922f343e528f2b3d310cf4238d24f81cf220791850425c5f0d02f3bf2341f815c13f32f0e7317ffff588e5a3d02fcd65efff55f68edb8532ae8013ef54f2f3f9d3f4f88bd9a255318e56ae05cf104827f86f544f4382b5f083f283f72ffef52622f02eac2f34864263f5fc21925ae7fb3fa8041f218e1fab0ea084049f20811f799fa0a26f9ab508431c7269fe5),
   (9032, 0x1249b424f153e7641f2f2206f281ce2f2c1916f642ffe55b5ede265f3f3daf8b9f549a4ff8014fa33f22d06fe55f2b38180194235ef3bf02125083f7834851f5f3f046d8913401ff871fa20e4b6103ffe50243f3762242b61cae644f8a4f47f88a0b51802570461cf9d36fd238b1e0b1bec1358cf75043a6cf70e5f022f52b3a9168bfc26ff6519f3f9159f2c2d6a9fe94832240254b3f9821018aff85b24f2b6f88f91cbb24c7e538e15923ff34e5621df2f08221802f0544fbd3827071f83f4ff4e6f313215250b15e),
   (9059, 0x1016a62489189f67bc8f3f6d21f2f29d05a372ff14f40245c52fff18c1c122b9b8fc15502bb558d3f64ff252405f33f1afa37b561262f0284b3e6f2cf86fdb6a32b28f51f4ff1915af4e504bb52051e6f3ab65f95129d621e582ff7076f8b02f015ff89f1853125ffa0584348b03f815c12e5af21073246726165f31bff2879f81ffcf4f524070e84238434645e2e8504538d0e5a3f0791803f225f8261eff24c81985f1fa206f464507c768f91c9f5549454f215896f462884fff8523a9540781f12322a29be510a584fa2ff),
   (8952, 0x14fae3480a6f3d0aee370552aff1e22655d683f3f9f25f562451f123f553f32f2ff192f04b05d06f25426f52626ff6a3a61345316dff727f2b12e0b49104b67df6ff322d04028f1ff9f1f10132a5c5ee6f438a05e11f1379b8a0d3fe9423485044f2729d9b9f2f3a6405fe32eb2d0249572fff0180e2496fa4fe9f8782221f5f312045262435f2e4febf673f02a9f56f5ffd0461c256ffce40b2f502a0211f1232b512bff85f262422e5016f0d03f6f19b47f2aafde01202bab292b3f5f5354588946109fa53f2e389f5f23e7),
   (8395, 0x16fd3450437531af7af1df1226e4e652a36f2105fffb48959f2e49bf86bf32cf70191b33ff25562f52052f6fb92a294cfdf42343b11f47fe9f6f87267ffd9151ff6519d3f922a31cf6211f482229f26b2557af7c46d3d01cb1bdf2126512affcba35f8ffd3b27b1f5e22245c24dfa346b56f9ff66f10571f54922b2f25e86d09fb8d0d67e3a01ff4c3f7057bff1ff84e052212cfb1f19a55209f810cf787ff388789758ee952f6e467b016f0571ff05f9f6420ae6732a8e9a64b67622d80548),
   (8554, 0x1b753215310b4b9f0526f2243a926f58f68d3a9ef67b3f3fff12027ca01ff42610d9b42b0197cdfff0156b4265b213ef086f75eb8295bf22ecd1f1624613a1fb1026ff612208b1b046154f4af48556459f08e22f5502451f5f32513e759b1551f12af1b013f3f4f197055e7946f4f88f820a922426214ff7f10d9a98513750a4fd03f5f69f14fa892a5010a31e970a4f22465f8ff425bc1826489b8423f3fb3f64286f61b0e2f1f1234e57ff39f5bd520a35426163fa05fc6fa3fe23515fff2535),
   (8501, 0x123b24c162761c23ffc7043f1f82bbd322a833ff5b95d05797323f1ff245862a262a373a2679551c7021e3842b29d26fb64058402783bf4fef22351251f1b268f0a92210e5544f2dff52ae1f7bc8129a580794b56b7df8854291c7e2057023f44ff6d295fb2012042684b85280a87f4cfb5207585509f27ff1928dff2768f4f211f71f8a3e191551ff891fffb01054344f15286d6429ef6222a291ff194ca32f6f28532f2c11f16bf61956f273f8fff36fdaf53f9ff2504df815266ff9f8341f9f),
   (8820, 0x1329f85453d32bb53f40de0a6516405d53462818b7f153ef4fb45e6e74f4525984af84c2a3b155526285f019244f2b2b108fe02217f51220258135758b9ea802f8ff2b402128ff437ff8f5927c6f571f40216b8a6faf1552ffb788943a853104cea6f3511f5f504b911ff2b20a2c731cea7f1268f85ff5401ce42315ff1cee194654628b5240bf34ec402fc1be6f0a4f25f0813f057b3f05f6e2b702a3723e4224f194e4ff94c25510ea254f156e22828d8af10b134373efb20814ff6f3e1bc2a6f),
   (8793, 0x159fa610b467c121f76849459f53a53f7f2f62a06f8420d0405885f7f1b263fbfe36f136f2483f88324b919251294919d4f543d955f1f84312e6819cf72379f9a88502fb05f6a610165f288646403ff82b27fd1f82f8859f35450d3f62464957b83f0d04868ac3ff562156f1ff1f2f052210408f5312ff10a3d29852a0dc5f223a9eb5f8022feff1358aff8a5076b2f39f131622aafa9cf181f44faff104b227ff5263f2f88e3a0762a311f4b04affb53a4f42c7623ff973fff41f287e642651325a0168554975223f),
   (9112, 0x1208bf0b46f36f165125e2047f2d05f32f32f346f252b31b596f5e21ffe1c6ff4f5f05f09ffc22fe2052456f8e0219127fa7fd255317f4232244f48e552535f7f167fff9f4f10d0287235b821294595402a2c2824379272ff41f73423fb29d285652f8535b21058ac5bf3464321258054eaf73f6a56f9f224ff33ff53213a4f56f2f2372804643fc1321803f215e80d5e02bfb65198241f6f7e53a3216212e264b0b11f75209f585581e1ff6557df17f52a582237538f98ab6faf5d0242944f421fa2c705424f554385bef0433f),
   (9351, 0x109fe792e2465f259fb821ff91c46f0d52c82285f3f235762feb85021655521b649a6e4624016cf6fd5be63f16f26b14f1857f4e6516a91646f9d38a9436ff05fe6764619f61c78c11f9f11f4b0b75833f3f55d4f4040b7c2faf10ac11fed80d34cfc1886f0a925586f4676a9bf3815fffe6401e23f05cf585b74f7ee880a621cd0758953f516126fb2022486fb94045071fd314f59ff65d5253523ff0d35228dbb65f4f450ee2a92a042c4e921250b469ff048268f325f01cf014f402f9a347f723d310735543164921580195f1ff),
   (9777, 0x126f25405cf194c2f5c41f8b70843248340251ff8734e9e516fb825be342537bc16a8862d57f6ffc856f8161e5baf29ff8cb10b5455654e8b533f242553255e8f220a65121f277f5f533f7622f20885d50a8e538467051ff168bf3d6e8bf02f2674f5d204670a7f127f524e07503f5e9f8f3a20a82675027204264806f9f45658b4ff2d02eea078551fd3f67297b80cf5fc2a2b94e04673706f21e0d25b9f39f18855250213fb864385408efcf94205f047f51e66ff04e03f51231045ff2279ddff2cf3ed2622480d06ff822505f6210a3872805a2b8),
   (9616, 0x12caffef61083f426f2e1fa0b4b52b3aec9f8f2981294b87f43f62cff3f23d5c10128ff404643f63f5459288f2b35b210a38494596f8121fa62bb4297ca0b123f3497046b7b237654825580227b9b3f4371f54592aaf6fd049f831ff54e809f5496fa32132faff538fffb103f121f7c1282550b4562bfc5f3f3228f611f16428940707266fa591226845232f03fef6214f40278895251202b43acb5b40a6f3f1fe5f02e85fcd85e93f3f2408f93f467b95fafa3e11f256f437cf973f8206f3f3f1e01c14f840bf8e3eb70e511f46f95b40a5e291ff6f42b2bc79),
   (9963, 0x1cfb51e5b2e4f40d6db3fbb67672c4b9481f284c26f4010a89d9cf2b456ea31083f46705d51f284234862bd5afbb70464355f26821c24ff6f4ca552af4059ff32f319257c2f6843a4f7bc483ddfd51ff23195b43f265f2e5085b41fa96f105d04e2af734aff957c3fa316e188082126cfa62b5a1f4833ff23b22f29186735f059f5bf231ffa64ff402465d925cf855f2912313f0b4c5425e3a616a29a80573ab281f8513480486b5b3f1621ccfb4345c462543123feaf2d01370ea537292482388e132f26439fa5205422ff22462d205a2052f7f2b22e21cffff),
   (9112, 0x1462241ff322f0d9f9540246b2fbff7226e16f059f723f5970d6d35d59d56f4f43127ff0d55b5322453cfef02a2265aff3fe1266f1b6f9168f6e152b5ff5106f7598216e22257c1624b0d293f2d681853433ff376f98a05d261fff5c763f82a85520bd082a91ff432faff37c554655e73fb2afd3f018e318ff3f5f3546cfa9b25f8e1f5f65de534b36fa655d827f2dffa051c49fc29f254e0a27fe8d07082f52343f8582ff13f6180434be97953fa65f38f2be09f23ffff8420d1ff05f0a3f04af215dff941f5e45cebe26f725ff43b2433f879a6),
   (9591, 0x1284c3f2fe24fe46854ff1c10b5545c13db1ff280e402512526547f5a22b7f8fccf23ff26a4f27324b93f42024b340755e2b34e34508f22b264afd085f52918047f4040d50b211fa02182625a9deb7f12046156f53f08a3f1f8b3f6f86fb2f05524073f8202f38bf08a94647f3f4cd0b10d7ff80150702f3225f7f55f8641ff3f2622408f0162d4f3ff342b01671fa5389f2f01923f41ff0701808fb202a322134562153b5823ffaf5b1256f5262d24f2404855c4ff2ef016b42559456e43f3704945e36f702fff437882ff5493faee0b15e623f434224f219),
   (10095, 0x1a356fb467c17fa23270272647f275204b3a1ffb94c10ecf79f7f2185202f352f23db3574f125505f38f6221cf56e2f352a52c2db58df40129fb94af254b63f192424f13f567042643132248834ff4622e521291c14f58544f1259224c5452081232783f3848e294c47ff3f0a1f194b1f43f1fa9f204509faff6f24e0120277f55f09ff9192a3216f3459ea0d3192d1f55f9a610ddf6fe84b564087370d1fdce12c1cfc1e65462b186f8e501c4613f29762f0126f4fdc123f95e486f316765f0875fff82b58af2426106f274fa3212505d26fdff21f43f9728232b48349102162),
   (9829, 0x1ec46a6f86f3d0b4253498104e83521957355722864ff58a0513f98f6f4ff7f22d04c1676bd8040401bafd1f7ff3f8e8fdf52b2e4e220882e16f354628bf625f323f46f3f5e054e6e12b26ef59221c5fff8ab3583f102184ff0d54f1048384cbb525f9f94c8511f82f1f82e7324046788ff3fa595fc7651c4022486f3f324e3bf26d25af6f8f5506ff340ef316b259f2f3f2b223a312ff1ff11f552f640bacf8312022e794cf649b9ff6d53b2f503f6f1bce1b532b2456104022f0b28ab06ff05fc28fe09f4b95f38461df1e65246f355f2550e5f802cf246e1b075835a52026f),
   (9830, 0x146425348e0135f88046465b3ff93f4e3d891c429106f44f17f5f2322f34e37641f1235452b8321af131b2921344f455fff67e1f4891c1ff3ff5825507894223a346f619271f273fe5c248af8f2b59b79a96f2fe232bd520e4b925f6ba1f41fe8d3a64925707ff70b436ff20121fd6f2563fef042ffa354ffebe286f1254f5510544fa0d349a340a6a1f6fe1ff8f08bb516be545ff4226102a05fc41f3f2462f6f9159551019b15c5a3a3702ffff0d040762123f8ff5d016a9f640128c248357052ba2e53f9ab2085f829f046b5825408a21fe1e63ff09fd6f86fe976f3101),
   (9219, 0x1551282583f68fc46f850167c2f058f622e76492121ffb4f82f3f9f1f542cfdf13849ae9522cf1021cf6510a2ff2f2af733ff4ffaf5b875e536fd9828726152cf8c4040e5b41f48e2b9a64372e2aff0435a3a03ff01321c7ff181fb194346b8f81f2fb8e025f53738d017f2f03ff95824b59541f2a25375ff27325d0bbcf848057ecf3a31cfdf25f9d23a98765842ff22f92dec5f9825842b640ef84f732270225f3a9f2fff0246fc249f1f86fe8522fb2925fb35f5c5f072b0d3f32723283f554867e35a0b408a9a1f4381dfd6f68fe68f682288),
   (9192, 0x1e3108fb3480797323f10576f6d026f5fc7c81951013e52192a5ffe1858af840a92b10191ff123d98b496f79572928a2fff647f7886f25352fbeb856f237619d08a20a8523f5ff5b40a1f7324bb8bc5d59549faf510e43ba6e54913576433f2cf6fb102fe61312616f616f05767057801b237919a94e24fcf522f4f5f2b6f25250e4c3fd1f429fc1ffd31b940a6f9f9813a29486aca022f24f2de9f34e0b49f80ae6b79401970e57bfff64264c6f453fdf703f192a6123794621e047f10461e862813f96ff02f32768f27f7af),
   (9245, 0x1954351281f4b6d0bf82afe79423286ff024868432f889acf341f10a850102f6544f723b55fb2c4523f921286faf840e4070b1e505f7ffe325495404921254ff7f85570215b69f19f2081ff55219d3abee2b65f01916f31538a2e223284ee986ff02450bfbc461c41f88f852539fba6bf674f78951b2b0122310429f234344f180bfca5615ff5f5853f0ddf8d0a97af1c5f8b86482dff2652f66fb192285f52b99fa4f2a8edff3f0db57f102815bc2fb02d232780b183e45b35156d21fdb97911ff297b0125085f264c75ff7b53f),
   (8927, 0x1d03f46f87f168822f9cf42b0ba981922870e549f611fcff01221f252f3f3a509f5b516518537cd206f56ffff9f8f678349432f084529f23f6b45670d0abe92101af2f3fb23a4f8b24586f9f1ff1fd0844fe555fe2645919b7502a9f28e2b32fcdc75ff73faf54223222f0e13f675022f979f51f706f756b2826f4051c2dbc494019f1f42504e2377f4225205f6f34611f551289431628a802cff20a2262492dff82a4fe2f3efdfe7e91b01c182ff11fffff80543459464648644f7081ec1c423816a070a6fdfe1836ff5dfa648),
   (8873, 0x1135f0a3f64615622d3f20e43f1fb8efb83e811fb102ebefffa36ff505ed250524049576b22aff40b1e052e273288f227f9ff63f13f7f82733fe41ff045e2ff108a06f5f371f84681eb504c103f4328d6f3f64c516b8822f3f204981b642af40ea922b2bbe24e059f182649e57e855583d0557613fecf8ff5f20b1ce1eaf2109fb841f3fa1f4229821344f3ff2ff1551f47f5431345e01af2101ec129b42cf83d66f105ef58358fff429b45237324cf1fd6fb0ef6db34862165d507048658f052431984828e204e6),
   (8316, 0x1555b55f61cf3a1ff1ff0cf4e1fa01b3a5af43d6ef07616d8b6f351640b4533fb453545943826ff325f7f43d95f0ef6ed521fa4f554ffa29512593f3f102fe3f35a4f18025f1f5bcf224b587f546584298fb3f6b5feb9543f50216bf3210467e4f15b014fe7ff1ff5f24f127f3fa53a5c120755344fa69f5844f11ff8e6f6bd1f2cfdb207c7b29822f07ffe2429b402f3f3549a2afb43f23f6126b5dc121f57c1bbff251370813fe5bc6f704355fb3a856409f1025857643d2bebaf5f835183bb),
   (8315, 0x14532e559f1621c28e6ff67b1f1228cf6f641f5522fe4fa7f4b382f8321b87f105ed67af52725071f277f219bf7f5f3436ffe68f072c12b32a0d08b44f5f22b508452ff3f41f2153fe043b82e12013a234b03fdaf12b31b013f501e9794344f84b3459f1ff2ffbf2503fa3f9a520489105f85af2f621ff1e316450d1f27262ae21fcf71f2792f9b23f1013f5048583873587979735ac450d61653fde5621b6a323ff96f19acfc46d35d51f7891076f31b23f06fe74fb70b157f73a376),
   (8157, 0x155515e32481fba0d0d8918081651ffed94502789fe54fa4f1282b537bbcb2cf846f1f216b2729f534018016a3f32f0d36f70ed65734911f73b41fd04619a20a208f0ac1048ca619a0845047f28f3a33fd1fe13f3ef07224f2e2165f1fb2812265437e3e9f164910791838a31eff2dcbf5010ac279842cfc154f6f7ff70182cf03f8cff520b85edc3f4970405f613a6f35f268fccf13464ff40aaff1fb1891351506f29f4ffb4226cf454f1ff2e75082585b1ff79ac51ff41f),
   (8475, 0x13f3fbd0735a97223b4226ea371ff97046f613a5835e24c1502bfcf917f756f5e32792a1f10a5df1b9e4e910b54b88b340d05fc49f26b22d048e03ff533ff6f27f43431925f7f168f62a0a3406ff2329fa676a5381049f36f7263f1ff71fd345e624598f6a3a83f01611f44fef52046842ff21b0405822e1676402ddfd2b20452b0762f06f210ede1f845b04021ffa6e4831c43210543fb315ff8540d536fe2d95a80434310165e3f4e80d0cfd357922f5526bf2313fc2fe09fa8bc),
   (8554, 0x1610cfe461228c71ff80cf46f6211ff252b31ff1679246f07023fb5525a2cbbd1f488085ef555b08a6498492e1880d6ef0765156737e2984556f32e15b51ff4fbac5a35bb436f217ff97025f532762192136f151fe72e65164973bf4f5d4fb7e50217f2f3f5b3eab26a53183840a02f06f2a6f2262e2b49ed03f131fff0408ab66f218e5205e73e6ff0542083fb4b53ac482237615eb54f4c786adfe14f8541f424f57ff5197e94cb48ffa941f2be51e50d4f552138e40456f29bbb2),
   (8502, 0x1e970212e94cf0ba0a3d952724f23f1ff2f26435d318598f6f1f44f43fc10b150276a3bae38a523b4df76b8e540eb1c4012340a0cfb4ec540acb101883e6fdb85075c5b9f9f54043d9a944f5d82dff011ff32a0484f8f4f2491256196f8405f0846ef4fed2fffc7376dff21e527f3f8154fd1f42283b1265407911f2d236f12611f752be4f432bba8861c8f985f2cb1c5f7f13823f9f43f9f5af2467022f852e0cff08756d04613d9464022f3f6f1f8764073735b211f19f3584b33f7649a),
   (9591, 0x1e0b483f22345b98a32516225f0ea612e59827cf7f102a23f253d9129a347f7b024051c168a208459f5e64c198756702b5e465a313481f221bdf5824ccff9ea2b6b519210d6e2102f232ae026f40458345c1527f71f22122327913759541f78ff821c40d3f807379d21fd6f3ba99f22f02fc84e35212ec2a5285b943d323f555f83161564685d05462f0e10a27f24e08426271f46f25e54f41ff2df104042b08aca527f7e3a7f432bf61c10811fd201820552a81f2a67af821289481f213439ff8025577f22f8294532f6f67e),
   (9697, 0x1be1924c81e25b8015801b22041ff1f1652a042868f97cedfff92a0a2e0db622438f29a3bed86be221208405fc22e2f62735a9756be5fce13f3f342e2853b7b5802e84046f09f4925f267236f467521fa262b23f7954925f7f22f2c461226541f7232a65fffe133f3fe426b273ea9e6f42cf54ffe05b4b6faf1e0a08452372508f9db5943d59ab6855b79d02f0e54804cb3f21af2255f2624503f135fe8ecb158cb8a264204856f924e23f96fa2bffd0b1e2c9f79761b26549f31e208481f486f36ff05bf89272cf2e31e0eb156ba65f0ae03ff),
   (9990, 0x1b23f4f81b9129a05f8829f223843735872af76105f3b225f2865f381312624804982b769ff21f4340511f2fdf135f3123183acf205d0d223e4ff73279f81f5f3e482dfa59ef229750761532f3f1f12823f1ff945c5b49cfdff240db9f318cfc522f80a3224cb2d2985f382427f28a32f256218523103fe5a8af455ff4862821b36f27b013f0a3f086f211f8a38b2a2b8041f21b08b75e319a820d0b4801673fe234919f57ff20431b7f53f4042261981be1ffb96f5f34ff40a043f9a5b7fef024af286f124f7565f8025d82cb2120723403f1b62b841f482ff8f05fe3736f84538),
   (9697, 0x14c1012b838247f28854e26481f846d6f621c2fe6a82bc2d0d4fd0b8526f258b6f822241f3feb453f6f0d9f8ff214f4af43812b922ba2ff4343b2b51286f6a31887ff9486a3431c163ff2cd5ff6ff6d35a6516103f4912021804ff11f18fff03f2b16feb082d58ecb25f685407504232b131e3758e0d1f4622f26e858afff04b3709f198480de28dfae340eefc25583fb49708102f019cf7c5a3516ae651804b56283f71ff953f732dff458c1835faf2702e2f86d2b0b274f6fb164e293fcf542ff43dc28e1df6f2f653ff352d585040be7ec1204206ff6d2913f),
   (9724, 0x17f461891615c82bb8bfe010a20d226755943f31c548b6f3f35e818358ba3242235ed92b4cf597343f3ab0a1f48ff5b8bf32242b295f09f5f89a913d05282e2a2234c4018524f4658422fff5356f43184f810b3fb27b8016fb37019f3bb2f854ffe50affa58ff102e18011f48e6a8358aff42341fd3b122619fffa640eae343138197c25701b57f6ff9f02b5f658b2b223f13d02a82af49f2b53849f2268f05e15679f1fef221f21e3e126f0e1910ba62a981252681efff6519b7088fc14ff624e7f3ffc462240a975c28f952b49d322fb25986fdaf25f379),
   (9591, 0x1af25f50d7ff2312c85d56e55f1f4205729f26f084851f404ff1343851324af4ff288f8013f259279f3ddf425df5f7f583fbf351327e5ff23fb2124fa2e05240a622a21feeadf2b15ff402a50b3ff08819f20b4b9acf6a62461c843a025d32e2b48ec25f92bf070210efece40d5af4bbe2323f122648af23f106ff314ff0138552404aff5022fe286f8052422044f8b819f92425ff25fc3f6f5d082463f2f26791381387236f55f583199ff62405cf27526705d0e76a7f73255510ef27f105f68f91643459229f759a8940a94ebffcf1941f4e6be79732279d6d),
   (9485, 0x1535faf25feff7e32f9723bf2aff23a385f9f2627cf2070d5954011fa351ff765de0244f1971f47f763f8a37294501c1af216ed8c22f232f313f322cf82125b4f753246270431251ffce41f4072e93f182262f892fcfec2fb83276dff275e208b22f223213d23f8017f5f91262a80a8022731525388f3f0792f1f108a9ef6f05d0168b2f599fa3131be2802d64c791ee56d3a264529167654805750eacf9491ee05f4ff3540d03fa6ef6f2868433fd208139f4e2bb31cf3f3fb3e2a53adf21e582fff0bb11ff01af5a53f058e795bba7ff29e58103f2f),
   (9246, 0x11f5e5cf197625123b494086f8431280a06ff1ffb54f2f012353fac42e61e8b8ff14f433f2fb09ffb20228f021292b4085cf3f4e02789d6249faf5128b4ff09f284079a5b56f5646888fe38a318ff14f840d55077f73103f4617ff0726a9a53f9d0522f3b1ec87684029ff613129d51f4013fb2cf0127f2a2506ff256f958a20452647fe10d3b76799f49108f06f5f657ffab3f4f7e676524051b3f0ef2208a29b522f6a024c16401b9812358a07922a0ee428ff3f6f246f91c2fbe56f3f05f89a8264fff2c9f571f8a04b6a26e2f535f915afd),
   (9219, 0x1efaf722948af13a4f136f1b889102f265123249fe538180845327619fe32e10cf9fa822208d6705d3fff6fd226734205a23289ff5952a07629ffdf16121f2f233f1b38210dc193f2a385b2a806f3f459704822617f40cf1c40e14fe5f4ff50a22ffcffff16a8b04c81e25341f6fa3f64bc762bf8b835277f195732192b5136fba610d531c221afd8531e8e012c12fff3f0a9b192541f5f268843f6a7f8588180257014f43ae016f91b924b6faf1651b68f65b3f461cb26fa012af28424f24c3fa2b0d3f051ff43f6a674ff0d91624ff58f),
   (8874, 0x110d07557f13f1f8bf372502ed3f21f701dfb43f823f7f765f6e5402a8c758597946f619765f2889a256ef86f3ede97cac3ffaf408222f3f21f24bdf1c5542013705f98723276d805ba5013f25cb846106f753243842fff95f345327cf23bed861fff851fd63fe575862132f3f0ac872b3bf2e4f102541f2dc7af15ff26fa8526fb385f052db1fed8070135d1f7b23225a9781f55f38e132f64580bf55ff54916526f4e019e2e70aff12532f9fe044ff62d59548616d9f05726279bf8af1345ff576403f1ff13228f502b),
   (8901, 0x18e404355fb208192fc2540154f3ff313279434e1fb2d0102fb289f02b5f6f2322fb085f022f82c43deb61df5b1e1f194af2a6f34e38abc8720723243f2612ebb98552d0a255c1532424fe52a2ff3f5f9453f628fbaf1268b1238ef6f6258f911f12b265a346dff51381ff4824faecf53a553a205d4f6f9fb1b1f128297cbf228c49cf426a8922f51ff376497c4b7f70132dff9f8e514f726216f8ff7945532e512682429ed59754f58b122341f57c71f3f5a3bf012e6737569f40154fe10166fe2a9f35f912233f),
   (8980, 0x154f192131af1ffd0b558527922f21f2e19702f6464229f04640a5ffe84b6f82502426288437af4645e06f1911ff5c85a02540d9488912057bafa9f5ece2f6b3f13f56d98191c2f0aca525b202ea53a87f1048550b5480852f37c29f1df4e65f3161585ccfb1010a26e44f840d2afee76fc22a2b945656f812353ff9f4f57267235a5911fa3d93ffc196fd565f1f5a97bb014f25f04072922f3f4f26ff86fcbb8f3456cf2a9fe2893f42ff4624520a1fd9750d043f0828227bc5a340ef1f78e2b01208f01232d89),
   (8715, 0x12f9e6f10b4256f81f3ff05d58fff29b46462102a5ff1c6ff33fcf3fcf43f2622f6b254b64641f13f36f1c8210b2b4e1f480a8049f63fdb3f50548349fedf46b27df13a34076f8315262d68a2580b11f1b94502543b3f1011f18ce41f6fa20215613f05a618559153137ff24238d532f0b243d4f135521e9f04343f22af9f5bf970487f426f8682f64b20135f02f6f07ff158ff2aff13cff5e326f1613a250216f805f35480e8246210781f5e9f2f94be24f21345229f1f3f2f92f561cb6f49d0b2fff12ff5f6d2958cff5358f),
   (9166, 0x17c5d1fa85b0d98f32a05f01083f11fe467310d04bc484fb1c4898522f3a3137b3e2f3ef6f0e7535fbff47f2f23a6a9b2522d0b77f2247f214fa25c461ff85245987c12081925d3a06f2e163f7613f836f24940a1ff5cbd4ff567af462185c4041f24e0ab7f2225f53f62278919585246fc22b82ab6a822058f9f1f126d97b0b2197c5212af1922b7bc8e82f32181f882155880819227958e19f043756cf453a3187f7cf7f5f04057315618310d3b7076f054235f02f6723101cf53a259f7f3fb8f1f486e9f2122676),
   (9352, 0x149f0d9f53132b22f3f0a22ff572325fe04315838210cf8ef32762f6e5709f5f5c6fd531016fb88b3f372625f8b074fa0548346425c22a5e21fd86f35dff28275c1ec10191835f058d28349f26225f51f7028fe93ffafe58736fd0489a83daf12506f150542321b6f82ec4e820cf4895bbd4fb224c6f4520547fa0258274fb9f85e6f492270812b83485fff7f131348053f4058459734b4f13f08a5ee68f2598fc29f555e10b164079a03f6f402dce4643f3f9d94234e20527b5615615b9b28f34c2f27fe7375e0211ff23f916429),
   (9831, 0x14532795402134048862a87f7b20546a9ac6f4523f2985fe22041f101af4c85b15af54864804c2f232f02b1643a22325dec1502b9f1cbf01045046a3519b13f954e6427f2541f15e03fa4f761385811f102f834312b317fab6a55262a3fee55049fff55d53f299f21c55222f0812c7dff36fb1922e16e2540d59f53bf3d532f0703f27b6729b85198f8e25324b643432f6f3429e2f3409fe5aaf16ae62d3f01b59586f52fb524fb88283f228723b9f5755dfb5497059f52a2bc5ef6f62a266f241f45b6adf491351b2c152fff32765f3fdffc4023f219f02fff),
   (9644, 0x110ba62581e802d26a58952131656ff8569f8cf70d044fd0d7fbf3f51f432a4f224891264e0109fa0d83f3a612ffb554202f9f3f94624b02434283437831c81e3123afff20728808f6dcf2b3845c2f59258d06fe2723249f4fb79404ff785b06fe21cabb51f40d9d6752e1f402a647fabbe0a955f24fb25f91025a3224e25ff2768a2af85f013a2043bee216552bf67822688f1ff2622f087251f1e1ff3f8c6f813b484f56ffc7370a3fe5af163fef0826f166f1b05f52b0d8983ff209f729462ef91079d954349a08aaf9f6f42fff3812292f1f403f11feb15b9),
   (9486, 0x12e2d56d6f831e65f534caff814f8fff4651949fc12645b69fed5b2028fb54f10e282fafd64b0464e8c7376f80a254f22f955515501cfe02d0189f058d6f04b6f0e402d646f6bef7f5f208f2646f0212fff83e19576f028194c49729405791b50d4f5123bf892fc15341f77f1b5fff2b5afa07322f1f85a95281250a6bf05b2246254ce1223431e4f570e52e543be8e6fb56f2583f2b1b591946e58d0ed310d3f6525d4f13dffb557cba5c42327208f3f3fb6134355f6f4fd23483a0526f40b2f36f857e50401cf08a9d268f3fc13f612b0579),
   (9352, 0x19f5022fc4921642640281e855b9586f3ff2805a2070585f6f59f1fb40d23e43f0a565f0cf1913d3fe2944f2cf1314f25a2048044fcf245b93f132274f6f1351b0d1f843f3fcdcb10e48e384ffdff2486f808724ff5ca80a02bf08bf821ffc44f5b51c43cfe51df105fafa1f4805fb3f2957676bf68f6a07e6f31c1523465254205ed598f69f819d64640138dcb1534021e4f524052f2340d55fff502a96f241f23f101c5d3dff7507bff246a1fab59f918b29167352fcb122262f2b6571f8b1cb14f84553fdfb13543434293f2f66f584b826bf9fff),
   (9804, 0x19222ed59fe56166f4e4f213f24f27616f29126d86ba3b8f265f013db2373489e2f1ff24f138422675354597985fb98522e47f555faf5fe20a2040728885649e2f3f256f2556a505f92405e2bf1ff3120aaf4bce5f3f95e498183a2651047fbe25fb0b4cf6452621b267640164640cfe46d3e5408b82a310105247f4204b911ff07ff8efb318026fd08f50d6212b61c276d264ff24b048265f54f104ff522f206f227b987df852f6f5019b7288048376e1011f162420493fa0a231ff6fb127f1c13d235195540151f8feeeeb2ff848b3211f240575c4ff25d),
   (10495, 0x124045e26d6219b5f96f1ffa9212af3f76465841f52e134e61596f219a2e0854532151ff3f02a082f7f2843f649ae254f818baf823f4926fd312cd070278316196f1be256b41f4bcf54f7919728013f7f11f183572b53bea32a34289f040703f41fa98193f49a0465180191951b2e223fff422624df46f5232845b621ff2b5f2e67bb205f62b4616f970a95fe7f21ce423180a2344ffc543a1f7bb0e162f92e189a4fe9f7235191282228b0e7021526f010e552f5b68f676764943f35884cf4f8492f231044f1ff252f261b5cd23f05f2640ed08425b3d913e2e2285f2bb02d533f13f9105f6f),
   (10628, 0x1321313f3a801621538f3d052123126f02103ff7f704340bf5921b0cf1ee7f8480185621952f20d7ff20ef6edb235f7ff6702212dfa38244f7ff21622f50224352e57ce16245b349425342ff5453f025a523b23f252138491346b1292f0b18918205402545c4bcf0cf42e025f23255d7f1019f316513e221922fb0750ed1f213fb62420a29f97c5fe08d1fcf71f42913a2df7051b31fff672628f98101be53708a0254b9fe0b495f65f23f838a6491b803f5a93fb4202f2fffe62124f543421f42ff6f2a26fb6210d041f52a52377f7e29196ff29f0183e523feb3fcfa043b1285352124f73a232d56121f7ff),
   (10628, 0x12126f223a81f8a32186f2df1af2de5e3221232224532fcd24f75850e4c22f7f3f41f12504622489732a01ff585f4f17f10240a8043fb81fe2e8b5217f4233f1af5f585640d0126f0246f58c40191016a62f5678e52ffa2e0213810b3f10cf1655f2b6429d05f66f48b225ff4010aff102a32f4f41ff86f88535f019f5b0aaf43d2234c49bbd35ef65fc13e810dff2dc4043422506ff676b723fe6216a05f201aff20befdf7622b10480a22af2f53244f3f24253e5a3f3a054251f244f516a535e5f3a4f6f5f046276b5a25b6108434e05732d6f323f84ff73eeea26492fe62a9a9422efff65f01af2f04613d8ff5e791),
   (10628, 0x112804042b23f2e64642205213210e7e50e44f5f21f181f7351c461596f5b728bce2fcba8c3f46464948afa20824c450842551fd29ea0543f53194b1f12688d1fd2c8b2132f3f022e108468d3fb9a99f6f45ee3d6a20e255f6b2761236f4cbd085f38ab93f5e5b42af4352f2e33f5f05a820a38b222f2ffa2af19a822328f2322f64526e21820b2f05a6a0a68f3858feb1fbb8a8bdf123b4c4c9f48041f82a057024b807c75ec586f8101af10b77fa084508522fb56707b2013a613e8139f2f2c197b23f954e024865d3527208a3f0b1c2126f3480db01536f19194922123a06fb2),
   (10628, 0x1802434e2ff55b4225cb7c4c7ff2136ffe58683f8f324084945043cff0108450882f31e9bb8f0408f57f786f825ff78ff8120279fc247f21b2fff2048df4327208e4520461c287384e051cf89bcf7205d52e329ff6218358cf75ff2f0155c41f2f82df1550495f628de345b340192d04b2c84681eec1853791942c488fff654eb622ac13d68cfd1f2f0405241ff37dfa2593ff8563ffaf401e5584f8f324b89d951cf237ee945044f56f1eb3842c4809fa5086f198f39f5e521234ff10138fff43421ff3f3511fbdff47f52f6f61cb2b422e35aaf4e20e432e87644f1829e72af53f5125ff221cb71f224912ffa3485825ff43),
   (10628, 0x1559f4807b5291b626ff6576dce405d06f16f61e6f04011ff5052f26542ff42c1b586f3ed0d024c4623fe5f5598215fff0ee17f2763f827e5c4502a6b7291261b2b0dffbf3554e524fcf72c5f0219a642321201e910ae01c22f342c25fee9185892be722afa5cf5e04cb21314f3f7343572b3f83a9f34bc10d5b7f78ff3f5491e38134891b6fafd0183480daf513f7f75019b43f972895f0d645ff5a3f53a04cb438b435e123f4f129a96f5f268ac584643b2f3f7fa0ed82327e65f014fe8185831c57df79b4263f7ff7cfc78c7ebcf08a6e7234ffd0b2fe26525845263f2b28db233ff25cfb05f04013f345),
   (10628, 0x17231354ff2f3f2ec45265f02bf349b7e4f22f2640b75344f28ae820efff82a82c40768d267322425262ba21f43f3f4f434bbdf4c814f1b5622f3f6f0283f246845ff46d1f2a9e2ae3495f229f2df2fc52723b706fa1ff264ce2f9ef2267621c1b4fb195cf70704b3bf6450240a02f09f1316b88b5d580e762d7fef6192737618358b435218e34b1f2584502aff1e38210485ee054bb31658b8cfd22c53f46f0a93ff2353f40e4076e8212055d3d6f6f6f62f2c48e8628a0587c1221fa4f2e7cdc7eb3702faf13f677f3f8d7f7021e3f6f610b467c49d62765e9f762105484f22fb048c4b3cf2d2342ff1e0),
   (10628, 0x1753a0425c6f5ee22f251f27ff5222fced385f2324c1b527ff3a22c5228d02e726432bef1f2725381e565dc1291657504bcde34049f68855f346f0d5b2823f348647f7ca8afaff134315cf67c2a851f842942280455949eb183405fb206ff20d04b91654852354bffb8fb3abb2625fe5ebbff9fd552354914f27820b1ff4827f528a2ff402e1b27f55fb8863f8a3224b35168198bf8e3ac7fff93f25210b3f9fa91b8684c7642628f628a0403ff59f58cecf51e26fc2fc15b95b1c75e5262a20b123ebf61c5fe6f0429a9d013bfc5ea889a39fa4f4234e267924349e5b3f482949134804ebc5e2),
   (10629, 0x11f780d62153252f3841ff55ffd6d35a2c74f2f0d5b92168f225835fdf70a911f2f3438513f1f44faff24ffcfb2f262e6f135b102aaf7c6ff7fe54958fc492f2c57291e9a91235e2fca58853fe23575ff16f8c123f65b70512fff58058d0162d1f12e3f610a043a3f6f5b047f8f35b10a5375345042055123f9e194ca523b8f06fe2458b593ff51fd7f48e08de0ef049f3225f3459541ff076463f4c570a8cfb013f86f1fa61565b2526ff3fe615e61df41fb12b052eb5f0429a047fe404eafd91ccf5f93f4e0bb14f197bc86f54e80428fff0e408848c2f0a6f25e57f76e4671f40882f3f6f954856f6cfa235e46435823f25e5),
   (10628, 0x165525f625f040aff813d5053f40d05eb427fa9d591801e9408a042c1261c13a83581202f9435f5ff1205246b28f35f05240525f0b7642643e3f13e126f021894257f7501502766f1ffa3d0132153f9872328481fadf182af186f5ec8558a0eb4dfb555123fe342ffa6f238f2bafd53f33f1280dc4081dfbf310480d4fe5e57af434b3fc2bcf8f3bf9d3135cf108e7cf20ac13f06ff50d2644f1b28250543f0756fe02f5bbb5ff44f1ff102b43f0279465480a0782322753ac54bff1dfb28a3b41fe4235dffd9e401c28ebd9e12619274f13f291b042b83822f019f2b26a9b7341fef2cfc41f1370cff534e2b),
   (10628, 0x19a351fff6f21f27ff451f492d9154f2270a6a05b4ff87c19104206f824043493f213d6e21640db20ef505aff5ef36f8fb6fb6a21f4385a3d081ff2705f5e64505d567ffcf7075043d655f6a82656f3f10bbf32b5d24f2780194058bfe293fba955f9e4c21688513db252af2f23fcf0d553462f58238a38122ff8513ffffc1858ca597081254f22d5085f940ef37baf1205dbec2f3228fe8c79d2bc2f53279b1e013a38f649f374f577f77fb74fa3d05fe3167ff1352a20524233f23f8422944f121fdfff20d3f836f77f214f84bc55aca1f244fe1e2c488e5ccf84052cf4affffe5576272e62582f3e45203f10e107ff5f0ee4),
   (10629, 0x1461671fa2226f9ae286f674f2885f9f2824ffc13d8b0ef88af42ff5e29ff2919fc24355f341f2a254f4c2b5f6bdee9bb1862a4f8a32b424ff043de3f911f1658b583f24262fc82ba8043f9525fe551fe246167c88fb22323ff5621e3f3ef520cf73216844f27355ab28204581f215c9fb6f70db6102e19f263f1012237e65fcd6ffff26cff6f5e6733f13f5853e5134254f4041f44fb8f3221c40435f946f26258b70127ff2288023f2bd1f7af40de897e92572e627b21f2e52f9750d3540eb6fd23f625757ff88e0a5326fa92723b211fd0ef56426491ffa4f2b6ffc213a27f2542532d9a2675c22f0874f5212863f1),
   (10628, 0x157fcfa0223ff085d595a3f96f52524642ffe1ff4c5453228f6dc7253b2a2b31615afb5404831c5f0a5cd041f7b5943f023ff3b1c2b1237229cfb73218313d6f802f823f4f86f22e12803f45cbf941f582549d09f5f26a4f462e2168a520519a9e53fab3e55f672022f250d6435f35fe355a237624ce461671fd54fb488ffba9e52123fff540855f3f85051c1ffd23f20701cf6f022ef54f2275832fc24ff46f046122dffe6fe6426b2d98585a62b2fc76729f221f5f3a3551594682193f2195b16d041ff57f462543225f61292812643b1550e7040d4f165402275ff18313ef23f63f4862103f52abc4556fff240),
   (10628, 0x14585028468faf24610780872505f646247f58a7f73276acf283f4fd4f2f9aecef940e1912208fec842049b1292e183bfe340493f73a2679f282910d383f1cf23fcf05432f373f9fff77f215583a081b623fdff2f04b0e43285e12b1f2fc84046d526f4f5ffff9702228288b4ff133fa89b81cb87288621fffe6f62a0885f1f5fe31ce4072b5b35d0b127f545ff5b1df8f911f4342cf1ff642c13fca39f79f29731ff705f1ff52ce1016156456e12b283e2f23210efb92582105d6f1fd561edf55243f61c72958fc2f5504ffa9d8b598d3219b3ffffdbb055252409f3ff9deafb70d98a0221045df780e437264261affe62182),
   (10629, 0x10242ff22e2458cf253a89faf4c764ecfb3523ff318229751f8e57823f67082fb91affe3a040d015589e1e86f21f44fa20b1c29f422b808723793f1fff22e4ff50876843e13b492f234533f42370d2b50ae676556fef31bb0aff570704610a01ce10a924ff2f5e86f340e5e5f59888a310ee191ffb708405f33f5faf750798b814fae61ff19f55b2ff55822e74f1532423f052f62e4b250d8dfef08d95402e405435e87c7321df12ca3e1e83fb56e5a3f2aff21fa08a23b255796ffb3f24f4223515675ca62faf19db323fd205d33fbbeac407e508b217f21019106fe43819bfcb8a26fe2651952f9f887f222),
   (10628, 0x15acfc1221ffbaf2a2b0106f213d1f82192105453f53f6f9846f0a327df2faf736fa4fb16493f213f802e7ff420161835b4c52a3102f0a2ff434c78e1f4e622d2235b8818088a04615be02f26f6f3422b6d91349573b21c5ef0451f4238f37623f129791253e554b63f104ffa5c1359f485591b1f8f1ff025ef6510576ef32b42655d0210e21b656ff3de2ff52a5b9e10761b292fe868f03fa586f2c11fdc83f135f94310e421fd31564c4cb2819f38f4f755c2f3f016468162f0108a62d95408121fed509ff9bf56a31387df6f7289d86726e2f3f28c22cf25f4f734521fe582b48e3188b2e24fd0dfff7f13b49f),
   (10629, 0x140150ab555ff527df4bff525f291504ff14f13258a02a0426f4fb480e7b33ffb68167254f821551f2f68f59b420452503f5240b10edb3f6fe502bde3ef537259f4f2214ffaf585f088405f1f2105f321c222f89242375502a5653ff31ffd64ee32135ac5704058272af49f67550162104ccff9f37949d5370b7b3e2a3cf72371fdc2a26d6d93fa50762f22b261b0822b1594b0e47f43f58805729e2e6ff32f2c216125850acae3f5805407b979528f65e12e50466f480522d2052ab98756e2453b753bd832842568f505fb537346f82223e21ffe2a02b162cff98a5c1ff2f86fe04ff88fe28b355f02f0),
   (10628, 0x135e2bf5646401e0d625874f221504ff212250753a922821258b1f425386f6f70cf4673f02a34b94086f2546faff89f0849249f2915c3ffc82854642cf28c27cf9f0b2827e20588a07b89e72b0487f5b734af485586f7feb76f8c3f5a4f6f42b2e55c132278b314ff6f319708a5267503fe129f056f8f37640824803fd66ffc2f3f55523a3765e40522f34952d2c2f4ff5943124f459f59fbce154fd08ae57fb54805f3f4f513813f6f0432122263f8ba91beff4261532e2d5e7fea07cd5b57f213846762f678fff610b1ff43db6e4b940103ffee35283f1928d531373fb6401c73785c82763f5d5592a3f50),
   (10629, 0x18313e5840510d7f848af4cf3bf5ffd6f5cb82fdf522e842594b4f5e8492183134af52a32f01ff73243213f046f51ffca8b35884b254f6fa88085a5ff48025fb3f68b13f23453279ac2b42b0d0559fe5f5cb495f4ff8941f52bdb3d5c3fb545e04e2617f2b7b38a6f3579541fd56f94eb041fa9f03ff6f1fa67ce855546b3f2821042321b387231862f2250cfa0278803f275319108cfe57022fe27f2bdb62822f27f25180e5f26e84528563f53fe73242affc14f491e91b95b4537ee38a33ff61af213b2f07ffd62fc216451f21921049f8323ffc8528552a34b84f734c219e2f08e4df22f23f0efafa23f6792d2),
   (10390, 0x1a286fdfffffb347fb27bbcd862d68ed06ff8e652454f8558d5be674f54af212891e9243f25ff212c8e18948c827ff52cffe52263f9f5242ff21042054232ba02457ffe836f13f7f2405d5cf017f47f4074f24b22058240461c4ca5344fef235b2d29be5f8026faaff35f5343fcac2f96f42982cfb25f01984c197595840852216f8b9f80a0826fd01e23e211fa58e2264c14ffffac548cf3123b4c513d05b47f2a55ff9fb6fd8623ffb3fe61df49518344f496ff9a5024502f2255802189f9f622708167826d32dee831ec73bfb2e4f4ff54804529dfff63f83f421fae93ff54f8fc58ea85021e348355f628e1),
   (10017, 0x12d834913f64083fb3fa85801e8853a27f5f9a63f44fa25dfa043f3f28289e5fedf5ae384c4e6553f8f623f125224f70b8ed63ffc1084550dca6464226b4044f1c5e1df1207658d4f123f7f4c42b35f5b0b3f6fe5b2f3409fea5233f4e2bc3fffff23d323f1679d3a3f1f5420189d55b0432498723fbc13f9b1c1c75850b6f81e2671f1bff2cf8f5c212b235432b7654c8e51c125858613f7f132f37567afe8136f5d3b7eb3814f2a58676b126f61ff49754fd6f8685755c1dfbf891ca53855f041f46b6f4ecfc2b19e5fe626f13d9f0d61ff45261262281925829ff5223f355),
   (9911, 0x116bfebffe82cf25408fbff131c5a918fffb6dff407e3b8affb40791231ff4b2ff1e013d0dbc1ffd7f5e876e221506f76214f752ff45b261e942941f40a232129b1206f701c55213f05f0ba6e1054223adf16a02e5f0123276483f589222f62493ff65e2a20b1c2d64293f87918e310b12048cfe2c2f27f226f4043f502fb3e40212561eb4f2f93f4dff2504cf50d6f84f16f9822f2224f58286f101976785fffe20221c4ff48ff107ffe45eff1af245954615654072ff16211ffe055e16f5252ff85247f521808bf676b4ff4562b849f9a025215cf06fd3450855d075313a6408bf827f),
   (10098, 0x181ffe22205f3a9e578e563f82195491370a8318503f3ff325f923f2fc84533fd2929ff859b21af7bcb49f86e44f705e4e1f43409f2e2f80e4ff2dc408108a6a92f3ac13211f4fffbdf405840a9212341f5d0d853a05f02585a3db912cfb25e327954526f048312fff3549fe9526f5f268454f4b3525844f2f013f324b2054c211f49a384b3f01621ff1013a3843b4ff22faf273a95425351cef2825cf6189872327615cfaf2a5b234e5b22046fb9dffae619f32f8b3a6185ffb53f2fc87b532f853db312610841f522f8b83161316cf705432f834319f6439f8a4f2437013884ce),
   (10017, 0x126d1f852a31257f16a8eff4057013f0d952120137be253282a87f8192bf08bfaf1236f8492a824fa20ef044f81224ff51f76d1f252136fd0a285b99ff3cf71f18043e855f025d53f3fcf040e215e6135a39fed1f81e3b4373f62425c13f7f428ff6f10d06f516f041f2f7f2a52c5fe2322f50a38f5557f7af212589f99ff3d59ae322e2161209f1851f841fb4945af554263f51ff421f1371fd0e85bf2c1cddfa09f87345916f957e05f01ff2727ff9f531624325f040210e73a504b0cf3fecf4255e3759e432b16f8206f86ff02a68d322821651b4f182af4013f954568f4ff34e53a987),
   (10443, 0x102aaf18c210810d95f05fc576f03fe516b4ff40491e99ff32461255e4f19b735851e05421f82286f1b6452b80bea057622f4f22421f4891231010b851532f9a91563f2f2af1b93f2467855024643796ff56aff8496f4af222ef2b238acb21595fc5227823dbb62450d3188941f1b1f43a850765f4ff05f08f64c2aff26ff223b53f186f384646b88737921cfaf2181f27375340bb12cd02585f6f2c8f31943ea98fb0218ff44ff3bf820e46284b52522202a6256fb40ed238193f19781f2f80761e082f357043121ffdf11f4914f222f0ee161868ef3ba93fa31b1ff014f84506ff26bb9f1880510a),
   (10417, 0x16526f40dc23fcff3f2e232288f354c47f12c6f4af52a355eb41fd0a0d3d924283f9f9fb344f54cb7c25f0251be5321ff76fff8f238f8c5a3f507621e3f234074f451fea627b802132453bd1f4ff24823f6ae55926f3f2ba52552bdf153279f2ff2d7f5f94226152055f8802b52a388fcef6516f318556121f43249d9fb622fc9f42047ff0824047f10482e25ff5bb52f6781f12af87c2b4255ffe43a98450276225ed610d04616ab6252f3f5084c136fae385d1ff6195126f2e0b49d01e01c5f0510dc5f8267299f21921c28f9136ff9f4fa022fe2c433f222f232f850b24c85d3f65b439fa5e64b9407),
   (9619, 0x1b0d3f2235fb0edc48ff21088124f1eff2f257f705426193f24855044f8843f27ff208a7f2e13510a9f38f62f21ff1f456fe673acf234223f502fff2bfce7cf56f31254ff23756fe1f156f0dca2ff2192e2101373f98f311ff31c9f406f2a7f8495466f14fd1f3f23fac10b51b66f25f594948324b2627e7f1df461204356fefafcff9f1f86f2ba83b7321599f1c4c29f2d021831672981ee0cfe1bffa3272358102fc78c127f6fe403f5f640129fe9d356f58524340e558f03fabb6a4f5e1b896f9f13f0845c58426408a0eab55ff76424fadfa58af4806f74f7c468d53f2888e),
   (9566, 0x1044f52d05542341f4598f507582943579813fb89a922f5c8bf0584c1c5542057057b355155df8f38b849cff9105f05259f8cf72821f5a258bc6f2107529bfb3855f6f7f13a021cd65f5bff2842295d59a265f8ff40573f23e47ff7f2cff26f643228d6f5988d2924e3e3ff313222a3e5d06ff2e08102f65705d3f1f1bc423761318cea6e2fc2198e7922f62738185618806f4c1088b105212ffe8d50780a1ffe0763f851ff6fdbdf8abcb1eff1676e213ed551f8dee525baf101327295212c157f2fec840d23fafb466fd27f22e105272bbe58),
   (9858, 0x135492186f08a9158640e16f81f2f326f4b976193f1b2ff4cf0581322eef981cd51f76750daf182562fc10189f310163f492f59d09fea26d02f261832f3ef05708ba7f4ff11f180ef5b2ff57c1502789f0222481fcfb73d0224970a3d9431e3121f8a229854cd9e6f8b8180cf2167e0b48e31cbf02f65fdf58e23fa2565fdf4941f24b529523f86f191edf73a283f9b183739f407642c13f921e3fe501e92d3d013f685d07557f45081628f4f2732f314f222b8e4c401b0b1234805123f05f31646221e3f6450224ffb7507b66ff2e29469f227532f3f8b804ffe1),
   (10204, 0x18208732a9a52cf8297b6f94504205b1925d7f7cf5628431322435ee7503f5255f3216813511ff23f02cfd52c493f48236ff4fbd22c813f9a05421f77f8e5fb61e2921b07621bfff2cde3404268db837826d61643e2f20d9d0120d3724f79b54088428df5ef5610432750d2b34b27f25512323f47f42ff846229f848ffb12596f2a80499f2b2e8709f2841f8f32dc217ff02429e8a9150e573a9b26f6f1ffd38132f2672fff6735f7f2211f2f2044f5e8bf022f8ff453584582283f9f835452640b44ff3d32fe043f372b85325188823d4f1c51af254028463f12b6f3f671ff8285621b),
   (9726, 0x1812e0d02246ab3bf93fa05fdff2622b421fa24f3f25e3f73f6f29b4e2978c76a08438f2507b613a268f1f1e83ef016e16f2895a0ba2ff5e16573bf8e50816121fdb256ef02a229f3582f25e074fa3129a05731af4531ff72fff50a340284b35521322786fbc16519705ef6f92e5f8c8f5ff5ddf282fe013f4f9ff654b0d627988f2c1eff49dcf4f54297c2f4ff1f43db861c435b7df461c4df453fe6f534e50b43fe9f25045cf01612cfe07676b221ff811f25e8f27fa50105515e0db6406f25a83183a808afff4f452bcb87ff4613f232a3a9b255d02a5af73b4e05f),
   (9619, 0x198181ffe39fb59f4e53f3bf03f54042081226e4e1f12e1f242af2164ff1580a86d0b54e61e51fa259240480ae3f922b4345ff2f2e358b25e405161ff86fbf3ed54fbf5b08a51f3f2fc19f8944ffff5435e8f0222d05275ff4c2153cff322191585b92812b3fe63f3fd4ff22610e1619f1f8126fe0281265f4ff53102a526f073554dfb516bfbe22808134502bb13fff429dc11f3ffaf8435a32158226466f15cf971f45388103f12e027286480588b16512af3f16a06f46bf64ffe6f3f25fcf6498d50210246f257f151f76aff1919a6213e2cf246e4e02f9a312676),
   (9540, 0x1b8044fb2f0126f87f423cf89f3ff5809ff9435f05d05eb4046f0d97c482232a3b2ba25e3d23e5f26f6b18cf235fc123423f23101b5bcd3126b1e02f265db3d591946b51533f1054082a92fdfbe4253e86fd4ffffa53816bf02a0ac161c4b01c8210825f0de51f57b29ef22022b19a62f5286a28b36f3f52f386f2a1f5425af4df3f4bc76f5977f9f22780165525b158291cdc154f707ff2726b7c1881fe59f7293ff6227081b95cf79454f16229f22138ac723a3bbf352de1ff3f6735f7ff4ff8b2c10554c4528ff26f52422e5011f5f9e13f6491b),
   (9885, 0x158e4022f3455205b1c126a1ff37262fdf4057ebe8508d4f3f1016b57af53f21af3fb51bc1b255e0b15b6241fd50e5156f9706f259f42928783405ba612988f01376a3227e0e40426ba82aff1fef5655846153212e925f346f912319ac13f025405cf4b886273f7fd87f253f40192fff4896fe1b39f5d0dc16f043f6f1fe5106f70465f2531e3f53450751f2d67082466f52e10b2f27f570757f7bb1f1803fcff36ff51f21e94621b34022f1f702725528efff22b922d98f801505eb2287e4f6f217f51295d34580e81c2d98f0451ff0429a94801ff4070a8c52f64e),
   (9806, 0x11ff86bf7f7c4679a1f462f25052de26b44ff50e522faf4928e5fe50d4f102a20eef08e156bf612ff132249b6f1c45940b2852f6faff65f59f5286705f07ff9f8a025e422255b66f42312b8053f1628d1f40e2a0420d3e492f9f03f2218298f2af4afd2b0d62b76f7ff8611f55f6f613132122ff55420401af48ff41ff01af1e9a627051280822284013ed3bf6b13bf54f52a208bfb82627235dceb5f582261ee622f226a06f2f05a294cfe4f704327e9d5e3540e5fff13f643bbe15613d22321c8408242881f423fff1351220d1f6f4c6f5d02d1f6f2bef3e51ff1ca250e9f),
   (9460, 0x1048227f54076792165de1f1505f97b0218c3f8d8531076f2084014f7b23f328f6187ffe8045bdf2a3552bba64377ff2ff81291615aff53423f61ffbdb9e732f21f822a1f191599f2a805f6764622874ff1f485c55f8220e4267281f82ba986ff85088874fe3f22a94382258a9faf1af76f0ed02affa3546f95e102fc1826e6ff2b5282322f6f3277f13b44f452022f82ff84312e047f26f4c285707c82a4f4625f1f2fca01ff732f0d853d4ff20bf20a3f1f2e4550e1c161ff2b8551af2e285f058f1fcfb2105e71ff7f521eb013f2ff5f83222fb018070a3d9f6f),
   (9646, 0x154538b9f22155070aff2fc855f4f456b783b3fd6a208d2e38137c24b618316f4ff64898a58382f202fe9dc196f70516576fc120552525fe5b28237c43246f551ffb01b2880d044fbf1f1e0b102fc2f37047f84016fe5026f6f10a2fff02aaf28ffff0524ff2a562126102d0138d26ab8297673f0a21ff6f0b1df7ce132bd617f7670e1264256f32e5b780bfe92a9544f88f2373f61289e44f2fe23271fd3216d9e570a340a7f16f65fe054262270ab9465f01658f4f120a22655d50193ff98120705f918e02f93fb23f5e4026f214f13eeaaff84f45e32d),
   (9912, 0x1915ffd3277f82a50b45e021e9fb280a532226f8b15affc44f510a0703f4053f3f1e3f9f36fd6d8b8316e13b169f46750761b562f33ff9480218206f8f5e322b2a2049aff7610b43fc55f02be425ffa08a57f58105f29f5043a21f1622f69f9f11f3f2f3f312b3527325819e75346d6843f6846b5467552559f3e58fdf71f8136ff0d2be3a20552f6524e08a01e0ea4f12861ff8fdf2f6211fb46f05f04232129792f2e05241f4c189167b012584f6ff3fb29f5646d6cf5fc244f7e65fc2f227f212340813fe09f1222054622a359ff3fdf570b10134015e50153a6b402f9843),
   (9991, 0x16405f051b9a9f56e22a4f162aff49e423f24f2fdf6f49a26f3193f2b8f4f81ff5f32102f250ed3f5805ee24268f38120a26de941f2cffaf4c1028518259f685e25de2925222482616f98fb9e41ff255b0855f9f50272324ffdb3aff120e84018886a327e8834561ec165d9a3a9f954af1083fe84946f9b8f205f3fbe5c13575889bf3cfa253a5bb5e6726825543162f079a3164c10b192b183513d3468b1972021561923f21b6480401533f2f9458b3f26cff05f01c16ef83fff451ff0d381254f16f33f79f80813255f051ff2a9f62f019d6f7f450510d51f6f12386f402a3f5),
   (10391, 0x127377f41f150259f15b0a6f3e4831cb5482b0731ff19723a259525d62bf32f6108a346f8ca2ff79a98fff84043164c79161204e0759dbc210a22e622f28222b2914f6f8f5523518cb228f5df5db5208162750ed07323fd643407c79f2cf23756216797314fe52134584feb2733f120b85d042916a072286757f2f64259522fc1ff210e2f35eb42eb913f0b5f33f11f9ff83f63f2164e533ff1fb14fa6f38558f7ff1f25fb322192f08211f192758558c55a6e45e649dffa80cf82131c16129764c1ff3ff68db868f9f01352d1f4684044f81cef2ec81291c27502f5314f1e3ed679f657522),
   (10496, 0x1d505fe25eaffbe63f15b3daff26228ba641fb25242e89a252229f7ff043551b2229b1268f611f12946248cae85e684349cff01642531922e1e53b8fe2ff8723a02a894b0428013f0d0402fb1f484f1c8225fbff1b223e541fa34e5342cb455c46a9b492122346f024c287c6f22f2e2979cf43f0d06f48ff46e5e43a91e2df53f25f6e8f9e10d68a6f234291af7208d6f0586f2f5313189f91254f1258b94ee6225ea34381aff85628a0431231ff2d2591aff3543fcf2b95799f5183a854ffbc456165129fe022f2051b355fff55ea2041f2b75ff3f3ff262462f2b1f79e162fe044f8b705f262134b3),
   (10471, 0x15462f58e2658101e50e46f3f6492f3f294e7fd0d8b91af723139f13b2f1f1ff824b53464af7911f17f8e2f20426a64ff16f04264016fbc9f4681eeff191b20ae1f78641f2f0a02d2345b08a085f2ff43123bf072c2faff02f56701fff310d3132bf593f7e25dfb57502d1fd9e55246a9499f3f72596f73226f816788b252bc73f05706fb1076f984985452cf1f47f2f0d2502a01ffa6a1f6f791ffdc8ab625f7f8552f262e2b123bf2e85b99f212cdaf512ca010a86f3403f275c108a92f594027622f0e16582156f92a375fff8b0704853cf2819f6192423e3f2bf02405438e13273f8e9122af2e55e88549),
   (9965, 0x155d81f812058486e708f2b013d38f285314f2ffff918b21fe72ff9f15291c44f1266f43a929fe1981853f6f9e28f37284fd23de07b04652f6e7c2f282ffac4fff6f9257233f5e18082e4264ff2458348ff44f137c1647ff8267be262a9f1fe46d292769f7508a20d65f31e33fbe49f53a2dff251f27cf2345e6452ff25482611f8f0d05128ff120553f54eec5525f9225a8529fe54f1af6f2f9a3e2ee3ff955f08b2a592ef01b0bfff152b6a342c4615074ff32a9a03fb825164b52e63f8101918324fff642c706fb5b212e52ced4f5585704523b8165fe648be2054ca4f8a6f2689f),
   (10629, 0x14b0d2384041f248cde201232d880405d8341f58f6d03f7eb05d0bf9f049f528532150a9b10b513a62f9729b1c8f3fe4f4b3819a3f2ff6fd98126f03ff238816fcf0a02b47f2d25621358a3e45ff8b427f4268f01ff1983f8f610108e2855f23a082f32552b43d0127ff3183bf4ff504ffe5459eef34052a053f46f011f464ee343d921c768431232f357654344f840436fe404940b468403f5d53122852b375e502a02a80521cfaf2e2432425343e55f0525407073f2523f3e6fd83249b1262a024b88505b28d7f8e3f5855e249b5eb5b5f92a3f013f6b40544f46f014ffff2f913f23a05d26213cf3f),
   (10524, 0x1841ff357c122053f40ef92fc131fff055f3d054352d0d2204e01ff21267625f32f02f50ab6402d65bb27233f8d85559213ab0e9fe7fff040bf34563f123241f12040751ff853d624e1f197055f85c46d3f91e36f224c4823e222e2f9b193f21551fb7e3fe02b431658136f7ff427ff3bd2e6f4f7ff83f49b109f2401aff9750a61c5823f6fd3131e348bb0b2554fff084b2658ffff9f010a0d4fd1f1623ff0139f8b9f161889152b4f21263f22de63f71ff2046fb93fb462b70b213426a231c76583fbb52ac6fe46b24322d087c86f14ff62fff102584041f2f01cd0a1fb41ff642ff79125ff6fb123764c8f21f9f13f58b340),
   (10311, 0x11c401e977fb28a2be7f2f80495b5f6ab50453f3ebd684258e267cf05f526f6f3a3f04891085105f081235165f7f4ee34af40ef801250852d02f2b4f7c11f8101ff10cfd295194ebb9f81f85f1f46f3bb275313f322a1feb2464df3fdc843d02f3ef56f610e12b02f8ff733f2888a34c7523fffd641fb192793f120d0496f14ffb232a5ffb21524f1251f8f23403ff9a05f89432735b8e5b3f752238bd3120d520d22fff613f56f36f8b257562de92f1f2165b822f3f22505f3a237b7fe5e4ffbd3bf3b16fb61804228c22a3a9a6457ffce11f9f436f3f16f91012e043f922d7f79a95408881534593f55),
   (10310, 0x18585f51f81bc2f2381654043fb808f2c4e95a2bff16bfe1f2e2ef4f192d0120762a3516153251231e1f426aff7ff822f318c468408f04023ffca610822cf709f1343fe5858625126f3ebd0d0be1c4c8252f61076d537c70bf4ff6d316453101c78652faf797955b78c55a3426a2684c2f25afd92762dff2f1fa05fb1f43514f43d9a1fd6d86b282103f134267291e7f403fd0dc2a31e61345cb812323fa52948b8fff236fd06ff1f41f19514f211f76de5322d2ec84070bf2b21ff37340d6f7f2b6ff3f21f22f2264c7074ff94621ff10bd226101641f191523be1ffd4f12ff2a04df8245ffd6480b),
   (10630, 0x1b2e58a531b594523fb05f68223fef262de8e6f03f4e7f10456f2355e22e10d622823f8420d6420a1f43d610acebf06f5f3ab05ee2b3f2101c46249f23f96f3f51984ee525019a4f213fe29a3185dfea256f26765216210e4312cf0438d94b27f23ff382f02fb6fc1b26451ff3a6425016f4f22d2949b5813ea0d0b2e4be7f2bd319216f61c74ff5c2e3f5274f812e674f42c48c734df28a6b5a2b4f4359f2420855e1283f3f4f218552be9f5c854b89f373487ff042b321835f0138a087b2df2a29278c2f5040b2b43f342658bf2351b056f8402f65b4e65f4f4e92f83fcf53f052a0434382ba9f1f),
   (10364, 0x123a319f982e761914f15ffd559423a50b5f7f796f4bcf040218673157f2218c4df785b29a4f1898f2c16b84826bd6f4f8546b5d04028f28b567924864ff2252a943a051044f7ffd29105494256f088198d8b94ff42bc25faf14f9fa8058223ff6ea6b48021e3b2a2298bf4fd6f5322192fff52f8803f2f26f0d87f813840726b27b23f64be0bd3d288b20d670242946e6fe5e7bdf738b22f3f022f538138dafa056ffffa02b15bb1ff59581204862ef09f2f02a253a32f565b1cf6f8202f9436ff1ffaf71f5843a03f5e1cbcf25f67370434043277fb7cf92f206fd62b3f8bf4f2f3bb450750229f6f216),
   (10311, 0x1b8a610b8f9f2223a6affe52f05f6f2947fe4834226795d3b2a68cff34c2f20e48554ff62ae05d018fff027252e0404e5b1ff568f3e15259431c8a1f21563f9f3fa1f5d3828f351267058f354619ecfef02a35fec7040b4ff2ecf84976521268d85aff97e642294864c11ff0cf429f8024627826213d0434c2a2922f6f1ff8b9403fcf86ff8045c2f4f24b070e4af212946f92f32792d0bd205fb204583f955e516f0a4f255f0221652f5e36f1c82d20194dfa54fd08873f91342af1340e6f2843fc5f91351c2a36f3f4585af8586fb15e52643fb523780109f19403f1e280438f20bfcfc4205f31e),
   (10630, 0x184bcb8e54882883581aff65f349f8684615502f0b5f4ff3a5355b422025eef65150e2a5583f591c6ffcfcb1e0a52026f84281f16fb355f232f52373d829762d9139f2257235f1f43f673bf0d7f2542591621ff4c450b5f0408d016422bff166f4502ddf4c5f52b02f3f622f0b2d05762284564084294b4ff26737fffb0bba61c7ffbedff465156f02548b6e6fdff42eb615c585f051cd2ffd267cd4f18af7e977fea02e55401019f3f0e5f625d373258bf85616431642202e1316a8624553f56b15b3f34951012e0ab263fb1024e5533f5aaff4f78c216f4f12642505b23f815354654592b43a22c16aaf),
   (10630, 0x184621235d69f14fe2e123f889adf3fd26279b15e64531988216fb61340a89ea33f1df5e407e6f6f22985fe22cd01386fd05108156e2485208495a37cd564e65f53498f6701cfee22cf341fe2dc16a6210a293f16f5070a250b6f138b2f3fbe01ff5a61853491834fff35d343225240e5f0701df43eb9f6f7280b40543e405f04aff026f27b68a08224646a37223553f733f1016213570ef2355f2cf206f7520465f1ff91084e04022d05fc4342dfdc41ffe3228daf192ed0b1640782622ea319f205e2e15b26156b486e43f6166f1b3faf729526ff50d0affd2cf0bcf188b1f8510bf57f25f33f103f),
   (10630, 0x19435461ff21ec15b262ae202f821f5516f6f9f025e2f353f13f084611f2f321ce5b2585e4562cf540e49f6192421ff070184ff1f9f4c2431e0b784fd503f4503f11ff2b9f02b404264325fb3e19d8bcf3f262f670bfe2b5c5d5224f27673f62feff2a083f5ef01affe2e1ff551f73e76401880a6276dcba37048236ff3f6f50d08dbb05e52d65437c2d2b68d6582a32248dfb1e09fd351343f22e61b864b0812ff708431ff6f135752e0cfef201fff01623f452946f51fd853a017fa25ff2753b10a2ff10542ff7355f1ff6f57f246a321b9431946183cfa8345355197df4af55d0b2f582c129cf783bf2c2810159b4e4f),
   (10630, 0x16f8b322fc2f3d3f6737e285ca0d1f123f501055b1ffb5825f9275523558135b4b2942edf17f1852502abb0138b7e1f5ee4ffa025f072fff0b21ffd6faff9bebf92182dfefc5b2f221f6f218222357ffe702f63fb77f45610d2b1fbf2c4b046fc7262a254f54b6a9f23fb91ecfc14fbbbd05b1349f057b97b8e61af21013fb641f48bc780dcb5b2f84f6fb755c5f913588522754ff67940491eca9a65f046212528ff2126515e68a65b8436f7b5801ff885f6f1ff6f3f8927621250154f244f1ff40d8322de0129811f105f08191b4fa3f5afbd22627501b2264ff82121f1613bfc1832485cf5595150524b6b81808a),
   (10630, 0x16519b9fd2985d83104232d313493f2f9e22426f346de0256f423408512346223f9f2f92a0723f89fff76a25205f6f021b7f23f1688b5732dbffa61c11f872234506f462150bf852076f6733ff38541f41fe439ffee50840223f463fd0576aec81927623f4b20ac4bb928e54231805ef5268210d836ff018af2188bff5858764675b68f7f2f21f5aaf1675340462fb2640efca61658f507bb01ca0ef01226f32f3f58b9b1c42be21ff2343f8af22426d854f1c13483e5b12346f28684b89722042229f6ef05d2ff2b5f3f023f2f63f225f348ff2b43123121fb192704ff249213214f542e295f1ff2322f055844f4),
   (10631, 0x1cf0d3a08f501eaf5b71f3fe582849ea253162d3f2ce1203fcf493f4cb2762454f40d5204b8089f57c824b20a85c2b519b558402725c581250a9cf3f42fff62705213a61592ef0bd80d9f7f5b275e8e53d5355211f156d3167ff43fff252f341f126a084829d27f258a5527fb22819f35a526b3ff31ff48df76d20572359f42505e2846f52b206f45c8bf38f20a232dc582122610b4ff4cfaff228c51250437598bf02bf59213f553a94e3bd52e611f1268f5e951952f62efca05f0882f1ff3795fc10a5e6fff2a867b3f014f88277ff6f83db1f2bf0212916a801926febf3a3528bef9aca3e126d89cf81be),
   (3694, 0x18584dff3522f6bf8c2f922a0b5120a3d6f03fd946279f04ee94c846401e7fd89198a81fa62feffbf028f23e728b025513f622fb32f29b77f3f5d9e5f3733f2218201c19f2645ff1349e44fd53582f8678b042fffb)]

def CP : List (ℕ × ℕ) :=
  CP0

set_option maxHeartbeats 8000000 in
theorem CERT_ok : walk 108795660965686084466 100000000 109937568534278953594 4096 520201 1 98961909 0 CP = true := by decide +kernel

end TFPTheta5

theorem solution
    (hbase : (108795660965686084466 : Real) / 2 ^ 40 <= Chebyshev.theta (98961910 : Real))
    (n : Nat) (h1 : 98961910 <= n) (h2 : n <= 99999999) :
    (((n : Real) + 1) - 2 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((109937568534278953594 : Real) / 2 ^ 40 <= Chebyshev.theta (100000000 : Real)) := by
  have H := TFPTheta5.leaf 108795660965686084466 109937568534278953594 98961910 98961909 100000000 4096 520201 TFPTheta5.CP TFPTheta5.CERT_ok
    (TFPTheta5.primorial_even 98961909 (by norm_num) (by norm_num)) (by exact_mod_cast hbase)
  refine ⟨H.1 n (by omega) (by omega), ?_⟩
  have H2 := H.2
  exact_mod_cast H2
