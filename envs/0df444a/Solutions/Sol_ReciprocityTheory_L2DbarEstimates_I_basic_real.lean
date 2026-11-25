-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.basic_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:14:41.335947+00:00
-- url     : https://prove2.me/submissions/dd4a1a53-d11d-48b6-9ca8-6ab253cb9bc4

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BasicExpBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (A ε : ℝ) (hε : 0 < ε) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) :
    let X := 1 + Real.log (1 + ε ^ 2) - Real.log (A + ε ^ 2)
    1 ≤ X ∧ 1 ≤ X + Real.log X ∧ 1 + 1 / X ≤ 2 ∧ X + Real.log X ≤ (X + 1) ^ 2 ∧
      X ≤ 1 + Real.log (1 + ε ^ 2) - Real.log (ε ^ 2) ∧
      A + ε ^ 2 = (1 + ε ^ 2) * Real.exp (1 - X) := by
  intro X
  have he2 : 0 < ε ^ 2 := by positivity
  have hQ : 0 < A + ε ^ 2 := by linarith
  have hlog : Real.log (A + ε ^ 2) ≤ Real.log (1 + ε ^ 2) :=
    Real.log_le_log hQ (by linarith)
  have hX : 1 ≤ X := by simp only [X]; linarith
  have hX0 : 0 < X := by linarith
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hlX' := Real.log_le_sub_one_of_pos hX0
  refine ⟨hX, by linarith, ?_, by nlinarith, ?_, ?_⟩
  · have : 1 / X ≤ 1 := by rw [div_le_one hX0]; exact hX
    linarith
  · have : Real.log (ε ^ 2) ≤ Real.log (A + ε ^ 2) := Real.log_le_log he2 (by linarith)
    simp only [X]; linarith
  · have h1 : (1 : ℝ) - X = Real.log (A + ε ^ 2) - Real.log (1 + ε ^ 2) := by simp only [X]; ring
    rw [h1, Real.exp_sub, Real.exp_log hQ, Real.exp_log (by positivity)]
    field_simp
end ReciprocityTheory.L2DbarEstimates.I
