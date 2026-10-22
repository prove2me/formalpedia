-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P03.logarithmic_inversion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T20:41:15.032518+00:00
-- url     : https://prove2.me/submissions/2bb03eb3-1210-48ad-a34a-3785255ed5ee

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03
noncomputable section

open QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable


theorem g73a_log_le_sqrt (u : ℝ) (hu : 0 < u) : Real.log u ≤ 2 * Real.sqrt u / Real.exp 1 := by
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have h1 := Real.log_le_sub_one_of_pos (x := Real.sqrt u / Real.exp 1) (by positivity)
  rw [Real.log_div hs.ne' (Real.exp_pos 1).ne', Real.log_exp] at h1
  have h2 : Real.log u = 2 * Real.log (Real.sqrt u) := by
    rw [← Real.log_rpow hs]; congr 1
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, Real.sq_sqrt hu.le]
  rw [h2]; have : 2 * Real.sqrt u / Real.exp 1 = 2 * (Real.sqrt u / Real.exp 1) := by ring
  rw [this]; linarith

theorem g73a_key (u : ℝ) (hu : Real.exp 1 < u) :
    (Real.log u)^4 < u^3 * (Real.log 2)^4 := by
  have hu0 : 0 < u := lt_trans (Real.exp_pos 1) hu
  have he := Real.exp_one_gt_d9
  have hl2 := Real.log_two_gt_d9
  have hlogpos : 0 < Real.log u := by
    have := Real.log_lt_log (Real.exp_pos 1) hu; rw [Real.log_exp] at this; linarith
  have h := g73a_log_le_sqrt u hu0
  have hs := Real.sq_sqrt hu0.le
  set s := Real.sqrt u
  set e := Real.exp 1
  have he0 : 0 < e := Real.exp_pos 1
  have h4 : (Real.log u)^4 ≤ (2*s/e)^4 := by
    apply pow_le_pow_left₀ hlogpos.le h
  have h5 : (2*s/e)^4 = 16 * u^2 / e^4 := by rw [div_pow]; rw [← hs]; ring
  rw [h5] at h4
  have h6 : 16 * u^2 / e^4 < u^3 * (Real.log 2)^4 := by
    rw [div_lt_iff₀ (by positivity)]
    have hl : (0.69:ℝ)^4 ≤ (Real.log 2)^4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
    have he4 : (2.7:ℝ)^4 ≤ e^4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
    have hu2 : 0 < u^2 := by positivity
    have : (16:ℝ) < u * (Real.log 2)^4 * e^4 := by
      have : (2.7:ℝ) * 0.69^4 * 2.7^4 ≤ u * (Real.log 2)^4 * e^4 := by
        apply mul_le_mul (mul_le_mul (by linarith) hl (by norm_num) hu0.le) he4 (by norm_num) (by positivity)
      norm_num at this ⊢; linarith
    nlinarith
  linarith

/-- Lemma A.1, pp.17-18: y is constructed from x, not an independent parameter. -/
theorem solution (x : ℝ) (hx : 0 < x) (hxUpper : x < 1/Real.exp 1)
    (hy : x * Real.logb 2 (1/x) < 1/4) :
    let y := x * Real.logb 2 (1/x)
    y / (4 * Real.logb 2 (1/y)) < x := by
  intro y
  have hx1 : x < 1 := lt_of_lt_of_le hxUpper (by
    rw [div_le_one (Real.exp_pos 1)]; exact Real.one_lt_exp_iff.mpr one_pos |>.le)
  set u := 1/x with hu_def
  have hu0 : 0 < u := by positivity
  have hue : Real.exp 1 < u := by
    rw [hu_def, lt_div_iff₀ hx]; rw [lt_div_iff₀ (Real.exp_pos 1)] at hxUpper; linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogu : 0 < Real.log u := by
    have := Real.log_lt_log (Real.exp_pos 1) hue; rw [Real.log_exp] at this; linarith
  have hL : 0 < Real.logb 2 u := Real.logb_pos (by norm_num) (by linarith [Real.add_one_le_exp (1:ℝ)])
  have hy0 : 0 < y := mul_pos hx hL
  have hy1 : y < 1 := by show x * Real.logb 2 (1/x) < 1; linarith
  have hly : 0 < Real.logb 2 (1/y) := Real.logb_pos (by norm_num) (by rw [lt_div_iff₀ hy0]; linarith)
  rw [div_lt_iff₀ (by positivity)]
  -- reduce to L < 4 logb 2 (1/y)
  suffices hs : Real.logb 2 u < 4 * Real.logb 2 (1/y) by
    rw [show y = x * Real.logb 2 u from rfl]
    nlinarith
  have hkey := g73a_key u hue
  -- logb 2 u ^4 < u^3
  have hL4 : (Real.logb 2 u)^4 < u^3 := by
    unfold Real.logb; rw [div_pow, div_lt_iff₀ (by positivity)]; exact hkey
  have hyx : y = Real.logb 2 u / u := by
    show x * Real.logb 2 (1/x) = _
    rw [← hu_def, hu_def]; field_simp
  unfold Real.logb
  rw [div_lt_iff₀ hl2]
  have : 4 * (Real.log (1/y) / Real.log 2) * Real.log 2 = 4 * Real.log (1/y) := by field_simp
  rw [this]
  have hlog1y : Real.log (1/y) = Real.log u - Real.log (Real.logb 2 u) := by
    rw [hyx, one_div_div, Real.log_div hu0.ne' hL.ne']
  rw [hlog1y]
  have : 4 * Real.log (Real.logb 2 u) < 3 * Real.log u := by
    have h1 := Real.log_lt_log (by positivity) hL4
    rw [Real.log_pow, Real.log_pow] at h1; push_cast at h1; linarith
  linarith


end
