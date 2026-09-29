-- Prove2me | solution 2 for TaoFivePrimes.mertens_product_error_absorption_512
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T23:39:30.810917+00:00
-- url     : https://prove2.me/submissions/53f93c16-76c8-4296-a447-b665bb4a8c00

import Mathlib
set_option maxHeartbeats 400000
open scoped BigOperators

private def ratDown (q : ℚ) : ℚ := ((⌊q * 1000000000⌋ : ℤ) : ℚ) / 1000000000
private def ratUp (q : ℚ) : ℚ := ((⌈q * 1000000000⌉ : ℤ) : ℚ) / 1000000000

private theorem ratDown_le (q : ℚ) : ratDown q ≤ q := by
  have h : (⌊q * 1000000000⌋ : ℤ) ≤ q * (1000000000 : ℚ) := Int.floor_le _
  dsimp [ratDown]
  exact (div_le_iff₀ (by norm_num : (0 : ℚ) < 1000000000)).2 h

private theorem le_ratUp (q : ℚ) : q ≤ ratUp q := by
  have h : q * (1000000000 : ℚ) ≤ (⌈q * 1000000000⌉ : ℤ) := Int.le_ceil _
  dsimp [ratUp]
  exact (le_div_iff₀ (by norm_num : (0 : ℚ) < 1000000000)).2 h

private def poly (u : ℚ) : ℚ := ∑ i ∈ Finset.range 20, u ^ (i + 1) / (i + 1)
private def rem (u : ℚ) : ℚ := u ^ 21 / (1 - u)
private def logLo (q : ℚ) (k : ℕ) : ℚ :=
  k * (6931471803 / 10000000000) + poly (1 - (2 : ℚ)^k / q) - rem (1 - (2 : ℚ)^k / q)
private def logHi (q : ℚ) (k : ℕ) : ℚ :=
  k * (6931471808 / 10000000000) + poly (1 - (2 : ℚ)^k / q) + rem (1 - (2 : ℚ)^k / q)

private theorem log_bounds (q : ℚ) (k : ℕ) (hq : 0 < q)
    (hlo : (2 : ℚ)^k ≤ q) (hhi : q ≤ 2 * (2 : ℚ)^k) :
    (logLo q k : ℝ) ≤ Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ (logHi q k : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hloR : (2 : ℝ)^k ≤ q := by exact_mod_cast hlo
  have hhiR : (q : ℝ) ≤ 2 * (2 : ℝ)^k := by exact_mod_cast hhi
  let u : ℝ := 1 - (2 : ℝ)^k / q
  have hu0 : 0 ≤ u := by dsimp [u]; rw [sub_nonneg, div_le_one hqR]; exact hloR
  have hu1 : u < 1 := by
    dsimp [u]
    linarith [div_pos (show (0 : ℝ) < (2 : ℝ)^k by positivity) hqR]
  have ht := Real.abs_log_sub_add_sum_range_le (x := u) (by simpa only [abs_of_nonneg hu0] using hu1) 20
  rw [abs_of_nonneg hu0] at ht
  have hlog : Real.log (1 - u) = k * Real.log 2 - Real.log q := by
    dsimp [u]
    rw [show 1 - (1 - (2 : ℝ)^k / q) = (2 : ℝ)^k / q by ring,
      Real.log_div (by positivity) (ne_of_gt hqR), Real.log_pow]
  rw [hlog, abs_le] at ht
  have hl2 := Real.log_two_gt_d9.le
  have hu2 := Real.log_two_lt_d9.le
  have hl2k := mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hu2k := mul_le_mul_of_nonneg_left hu2 (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hpoly : (poly (1 - (2 : ℚ)^k / q) : ℝ) =
      ∑ i ∈ Finset.range 20, u ^ (i + 1) / (i + 1) := by
    simp only [poly, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_sub,
      Rat.cast_one, Rat.cast_ofNat, Rat.cast_add, Rat.cast_natCast]
    rfl
  have hrem : (rem (1 - (2 : ℚ)^k / q) : ℝ) = u ^ 21 / (1 - u) := by
    norm_num [rem, u]
  constructor
  · simp only [logLo, Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_ofNat]
    rw [hpoly, hrem]
    linarith [ht.2]
  · simp only [logHi, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_ofNat]
    rw [hpoly, hrem]
    linarith [ht.1]

private def corrTerms (p : ℕ) : ℕ := if p < 47 then 20 else 2
private def corrPoly (N : ℕ) (u : ℚ) : ℚ := ∑ i ∈ Finset.range N, u ^ (i + 1) / (i + 1)
private def corrRem (N : ℕ) (u : ℚ) : ℚ := u ^ (N + 1) / (1 - u)
private def corrLoExact (p : ℕ) : ℚ :=
  1 / (p : ℚ) - corrPoly (corrTerms p) (1 / p) - corrRem (corrTerms p) (1 / p)

private theorem correction_lower_exact (p : ℕ) (hp : p.Prime) :
    (corrLoExact p : ℝ) ≤ Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hu0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hu1 : (1 : ℝ) / p < 1 := (div_lt_one hp0).2 (by linarith)
  have ht := Real.abs_log_sub_add_sum_range_le (x := 1 / (p : ℝ))
    (by simpa only [abs_of_nonneg hu0] using hu1) (corrTerms p)
  rw [abs_of_nonneg hu0, abs_le] at ht
  have hpoly : (corrPoly (corrTerms p) (1 / (p : ℚ)) : ℝ) =
      ∑ i ∈ Finset.range (corrTerms p), (1 / (p : ℝ)) ^ (i + 1) / (i + 1) := by
    simp [corrPoly]
  have hrem : (corrRem (corrTerms p) (1 / (p : ℚ)) : ℝ) =
      (1 / (p : ℝ)) ^ (corrTerms p + 1) / (1 - 1 / (p : ℝ)) := by simp [corrRem]
  simp only [corrLoExact, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  rw [hpoly, hrem]
  linarith [ht.1]

private def corrLo (p : ℕ) : ℚ := ratDown (corrLoExact p)

private theorem correction_lower (p : ℕ) (hp : p.Prime) :
    (corrLo p : ℝ) ≤ Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ) := by
  have h : (corrLo p : ℝ) ≤ (corrLoExact p : ℝ) := by
    exact_mod_cast ratDown_le (corrLoExact p)
  exact h.trans (correction_lower_exact p hp)

private def harmonicLo (n : ℕ) : ℚ :=
  ((∑ i ∈ Finset.range n, (1000000000000 / (i + 1) : ℕ) : ℕ) : ℚ) / 1000000000000

private theorem harmonicLo_le (n : ℕ) : harmonicLo n ≤ harmonic n := by
  unfold harmonicLo harmonic
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  have h : ((1000000000000 / (i + 1) : ℕ) : ℚ) ≤
      (1000000000000 : ℚ) / ((i + 1 : ℕ) : ℚ) := Nat.cast_div_le
  calc
    ((1000000000000 / (i + 1) : ℕ) : ℚ) / 1000000000000
        ≤ ((1000000000000 : ℚ) / ((i + 1 : ℕ) : ℚ)) / 1000000000000 :=
      div_le_div_of_nonneg_right h (by norm_num)
    _ = (((i + 1 : ℕ) : ℚ))⁻¹ := by ring



private lemma growth_bound (x a : ℝ) (hx : 512 ≤ x) (ha : 0 < a)
    (hbase : a⁻¹ ≤ Real.log 512) :
    Real.log x / x ^ a ≤ Real.log 512 / (512 : ℝ) ^ a := by
  have hb : Real.exp a⁻¹ ≤ 512 := (Real.le_log_iff_exp_le (by norm_num)).mp hbase
  exact Real.log_div_self_rpow_antitoneOn ha hb (hb.trans hx) hx

private lemma quarter_sq (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num
  exact (Real.sqrt_eq_rpow x).symm

private lemma third_cube (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

theorem solution (x : ℝ) (hx : 512 ≤ x) :
    2 / (Real.sqrt x * Real.log x) + 1 / (⌊x⌋₊ : ℝ) ≤ 4 / (Real.log x) ^ 3 := by
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog512 : Real.log (512 : ℝ) = 9 * Real.log 2 := by
    have := Real.log_pow (2 : ℝ) 9
    norm_num at this
    linarith
  have hlo : 4 ≤ Real.log (512 : ℝ) := by
    rw [hlog512]; linarith [Real.log_two_gt_d9]
  have hhi : Real.log (512 : ℝ) ≤ 25 / 4 := by
    rw [hlog512]; linarith [Real.log_two_lt_d9]
  have hspos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hs512 : 0 < Real.sqrt (512 : ℝ) := by positivity
  have hs512lo : (112 / 5 : ℝ) ≤ Real.sqrt 512 := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 512 by norm_num)
    nlinarith [Real.sqrt_nonneg (512 : ℝ)]
  have hg2 := growth_bound x (1 / 4) hx (by norm_num) (by norm_num; exact hlo)
  have hp2 : (Real.log x / x ^ (1 / 4 : ℝ)) ^ 2 ≤
      (Real.log 512 / (512 : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
    gcongr
  simp only [div_pow, quarter_sq x hxpos.le, quarter_sq 512 (by norm_num)] at hp2
  have hbase2 : (Real.log (512 : ℝ)) ^ 2 / Real.sqrt 512 ≤ 7 / 4 := by
    rw [div_le_iff₀ hs512]
    nlinarith
  have hlog2 : (Real.log x) ^ 2 ≤ (7 / 4) * Real.sqrt x := by
    exact (div_le_iff₀ hspos).mp (hp2.trans hbase2)
  have hg3 := growth_bound x (1 / 3) hx (by norm_num) (by norm_num; linarith)
  have hp3 : (Real.log x / x ^ (1 / 3 : ℝ)) ^ 3 ≤
      (Real.log 512 / (512 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 := by
    gcongr
  simp only [div_pow, third_cube x hxpos.le, third_cube 512 (by norm_num)] at hp3
  have hbase3 : (Real.log (512 : ℝ)) ^ 3 / 512 ≤ 511 / 1024 := by
    have hh : (Real.log (512 : ℝ)) ^ 3 ≤ (25 / 4 : ℝ) ^ 3 := by
      gcongr
    nlinarith
  have hlog3 : (Real.log x) ^ 3 ≤ (511 / 1024) * x :=
    (div_le_iff₀ hxpos).mp (hp3.trans hbase3)
  have hfloor : x - 1 ≤ (⌊x⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one x
    linarith
  have hfloorpos : 0 < (⌊x⌋₊ : ℝ) := by linarith
  have hlog3floor : (Real.log x) ^ 3 ≤ (⌊x⌋₊ : ℝ) / 2 := by
    nlinarith
  apply (le_div_iff₀ (pow_pos hlogpos 3)).2
  have hfirst : 2 / (Real.sqrt x * Real.log x) * (Real.log x) ^ 3 ≤ 7 / 2 := by
    field_simp
    nlinarith
  have hsecond : 1 / (⌊x⌋₊ : ℝ) * (Real.log x) ^ 3 ≤ 1 / 2 := by
    apply (mul_le_mul_iff_left₀ hfloorpos).mp
    field_simp
    nlinarith
  nlinarith
