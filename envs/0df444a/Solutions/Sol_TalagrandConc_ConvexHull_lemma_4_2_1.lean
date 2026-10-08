-- Prove2me | solution 1 for TalagrandConc.ConvexHull.lemma_4_2_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:41:29.98792+00:00
-- url     : https://prove2.me/submissions/6c102123-7305-490b-a4aa-87af5ecf6ccc

import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic



namespace TalagrandConc.ConvexHull

open scoped ENNReal

lemma xi_one_sub (α l : ℝ) :
    xi α (1 - l) = α * l * Real.log l - (1 + α * l) * Real.log ((1 + α * l) / (1 + α)) := by
  unfold xi
  have h1 : (1 : ℝ) - (1 - l) = l := by ring
  have h2 : 1 + α - α * (1 - l) = 1 + α * l := by ring
  rw [h1, h2]
  ring

/-- The real value of the term at `l`, written as a single exponential. -/
lemma term_eq (α r l : ℝ) (hr0 : 0 < r) :
    r ^ (-(l * α)) * Real.exp (xi α (1 - l)) =
      Real.exp (Real.log r * (-(l * α)) + xi α (1 - l)) := by
  rw [Real.rpow_def_of_pos hr0, ← Real.exp_add]

/-- Lower bound: `log D ≤ E(l)` for all `l ∈ [0,1]`, `D = 1 + α - α r`. -/
lemma lower_bound (α : ℝ) (hα : 0 ≤ α) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    Real.log (1 + α - α * r) ≤ Real.log r * (-(l * α)) + xi α (1 - l) := by
  rw [xi_one_sub]
  have hD : 0 < 1 + α - α * r := by nlinarith
  have h1α : 0 < 1 + α := by linarith
  have h1αl : 0 < 1 + α * l := by nlinarith
  have hαl : 0 ≤ α * l := mul_nonneg hα hl0
  -- (b)
  have hb : 1 - (1 + α * l) * (1 + α - α * r) / (1 + α) ≤
      Real.log (1 + α) - Real.log (1 + α * l) - Real.log (1 + α - α * r) := by
    have hz : 0 < (1 + α) / ((1 + α * l) * (1 + α - α * r)) := by positivity
    have h := Real.one_sub_inv_le_log_of_pos hz
    rw [Real.log_div h1α.ne' (by positivity), Real.log_mul h1αl.ne' hD.ne'] at h
    have e : ((1 + α) / ((1 + α * l) * (1 + α - α * r)))⁻¹ =
        (1 + α * l) * (1 + α - α * r) / (1 + α) := by
      rw [inv_div]
    rw [e] at h
    linarith
  -- (a)
  have ha : α * l - α * r * (1 + α * l) / (1 + α) ≤
      α * l * (Real.log l + Real.log (1 + α) - Real.log (1 + α * l) - Real.log r) := by
    rcases eq_or_lt_of_le hl0 with h0 | hpos
    · subst h0
      have : 0 ≤ α * r * (1 + α * 0) / (1 + α) := by positivity
      simp only [mul_zero, zero_mul, zero_sub]
      have : 0 ≤ α * r * (1 + 0) / (1 + α) := by positivity
      linarith
    · have hz : 0 < l * (1 + α) / ((1 + α * l) * r) := by positivity
      have h := Real.one_sub_inv_le_log_of_pos hz
      rw [Real.log_div (by positivity) (by positivity), Real.log_mul hpos.ne' h1α.ne',
        Real.log_mul h1αl.ne' hr0.ne'] at h
      have e : (l * (1 + α) / ((1 + α * l) * r))⁻¹ = (1 + α * l) * r / (l * (1 + α)) := by
        rw [inv_div]
      rw [e] at h
      have h2 := mul_le_mul_of_nonneg_left h hαl
      have e2 : α * l * (1 - (1 + α * l) * r / (l * (1 + α))) =
          α * l - α * r * (1 + α * l) / (1 + α) := by
        field_simp
      rw [e2] at h2
      linarith
  have hlogdiv : Real.log ((1 + α * l) / (1 + α)) = Real.log (1 + α * l) - Real.log (1 + α) :=
    Real.log_div h1αl.ne' h1α.ne'
  rw [hlogdiv]
  have hsum : α * l - α * r * (1 + α * l) / (1 + α) +
      (1 - (1 + α * l) * (1 + α - α * r) / (1 + α)) = 0 := by
    field_simp
    ring
  nlinarith [ha, hb, hsum]

/-- At `l* = r / D` the value is exactly `log D`. -/
lemma attained (α : ℝ) (hα : 0 ≤ α) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    Real.log r * (-((r / (1 + α - α * r)) * α)) + xi α (1 - r / (1 + α - α * r)) =
      Real.log (1 + α - α * r) := by
  rw [xi_one_sub]
  have hD : 0 < 1 + α - α * r := by nlinarith
  have h1α : 0 < 1 + α := by linarith
  have e1 : (1 + α * (r / (1 + α - α * r))) / (1 + α) = (1 + α - α * r)⁻¹ := by
    field_simp
    ring
  rw [e1, Real.log_inv, Real.log_div hr0.ne' hD.ne']
  field_simp
  ring

lemma lemma_4_2_1_core (α : ℝ) (hα : 0 ≤ α) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (⨅ l ∈ Set.Icc (0 : ℝ) 1, ENNReal.ofReal (r ^ (-(l * α)) * Real.exp (xi α (1 - l))))
      = ENNReal.ofReal (1 + α - α * r) := by
  have hD : 0 < 1 + α - α * r := by nlinarith
  apply le_antisymm
  · have hl0 : 0 ≤ r / (1 + α - α * r) := by positivity
    have hl1 : r / (1 + α - α * r) ≤ 1 := by
      rw [div_le_one hD]; nlinarith
    refine (iInf₂_le (r / (1 + α - α * r)) ⟨hl0, hl1⟩).trans ?_
    rw [term_eq α r _ hr0, attained α hα r hr0 hr1, Real.exp_log hD]
  · refine le_iInf₂ fun l hl => ?_
    apply ENNReal.ofReal_le_ofReal
    rw [term_eq α r l hr0, ← Real.log_le_iff_le_exp hD]
    exact lower_bound α hα r hr0 hr1 l hl.1 hl.2

end TalagrandConc.ConvexHull

open TalagrandConc.ConvexHull


theorem solution (α : ℝ) (hα : 0 ≤ α) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (⨅ l ∈ Set.Icc (0 : ℝ) 1, ENNReal.ofReal (r ^ (-(l * α)) * Real.exp (xi α (1 - l))))
      = ENNReal.ofReal (1 + α - α * r) := by
  exact lemma_4_2_1_core α hα r hr0 hr1
