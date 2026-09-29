-- Prove2me | solution 1 for TaoFivePrimes.mertens_product_error_absorption_512
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T22:48:27.376986+00:00
-- url     : https://prove2.me/submissions/aa83eb60-1a8e-4333-bd31-7a87dbfab15f

import Mathlib

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
