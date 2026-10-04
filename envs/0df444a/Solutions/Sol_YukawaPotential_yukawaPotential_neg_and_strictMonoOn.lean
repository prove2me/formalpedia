-- Prove2me | solution 1 for YukawaPotential.yukawaPotential_neg_and_strictMonoOn
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T15:10:10.992759+00:00
-- url     : https://prove2.me/submissions/577b3489-bf47-42b0-a32e-534420da5dad

import Mathlib
import Definitions.Def_YukawaPotential_Defs

open MeasureTheory Filter Topology

open YukawaPotential in
theorem solution (g α m : ℝ) (hg : g ≠ 0) (hα : 0 < α) (hm : 0 ≤ m) :
    (∀ r : ℝ, 0 < r → yukawaPotential g α m r < 0) ∧
      StrictMonoOn (yukawaPotential g α m) (Set.Ioi 0) := by
  have hg2 : 0 < g ^ 2 := by positivity
  have hαm : 0 ≤ α * m := mul_nonneg hα.le hm
  refine ⟨?_, ?_⟩
  · intro r hr
    unfold yukawaPotential
    have he : 0 < Real.exp (-(α * m * r)) := Real.exp_pos _
    apply div_neg_of_neg_of_pos _ hr
    have : 0 < g ^ 2 * Real.exp (-(α * m * r)) := mul_pos hg2 he
    linarith [neg_mul (g ^ 2) (Real.exp (-(α * m * r)))]
  · intro a ha b hb hab
    simp only [Set.mem_Ioi] at ha hb
    unfold yukawaPotential
    have hEa : 0 < Real.exp (-(α * m * a)) := Real.exp_pos _
    have hEb : 0 < Real.exp (-(α * m * b)) := Real.exp_pos _
    have hle : Real.exp (-(α * m * b)) ≤ Real.exp (-(α * m * a)) := by
      apply Real.exp_le_exp.mpr
      have : α * m * a ≤ α * m * b := mul_le_mul_of_nonneg_left hab.le hαm
      linarith
    have key : g ^ 2 * Real.exp (-(α * m * b)) / b < g ^ 2 * Real.exp (-(α * m * a)) / a := by
      rw [div_lt_div_iff₀ hb ha]
      have h1 : g ^ 2 * Real.exp (-(α * m * b)) * a ≤ g ^ 2 * Real.exp (-(α * m * a)) * a := by
        apply mul_le_mul_of_nonneg_right _ ha.le
        exact mul_le_mul_of_nonneg_left hle hg2.le
      have h2 : g ^ 2 * Real.exp (-(α * m * a)) * a < g ^ 2 * Real.exp (-(α * m * a)) * b :=
        mul_lt_mul_of_pos_left hab (mul_pos hg2 hEa)
      linarith
    have ea : -g ^ 2 * Real.exp (-(α * m * a)) / a = -(g ^ 2 * Real.exp (-(α * m * a)) / a) := by
      ring
    have eb : -g ^ 2 * Real.exp (-(α * m * b)) / b = -(g ^ 2 * Real.exp (-(α * m * b)) / b) := by
      ring
    rw [ea, eb]
    linarith
