-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength.prim_zero_of_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:10.797935+00:00
-- url     : https://prove2.me/submissions/d7040503-11e1-4eda-9c8b-599617df041b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_PrimZeroOfNonpos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
open ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength
namespace ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength
theorem _root_.solution {f : ℝ → ℝ} (hf : ∀ x, x ≤ 0 → f x = 0) {t : ℝ} (ht : t ≤ 0) :
    prim f t = 0 := by
  unfold prim
  rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_]
  · simp
  intro x hx
  rw [uIcc_of_ge ht] at hx
  exact hf x hx.2
end ReciprocityTheory.L2DbarEstimates.F.EulerCharacteristicLength
