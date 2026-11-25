-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.unwBack_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:57.194861+00:00
-- url     : https://prove2.me/submissions/6edebd8d-68df-4424-8cd5-d1a163e55696

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackA

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
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} [TopologicalSpace M] (K : Set M) (hK : IsCompact K) (F : M → ℝ)
    (hF : Continuous F) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, F x ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have h1 := hC x hx
  rw [Real.norm_eq_abs] at h1
  exact (le_abs_self _).trans (h1.trans (le_max_left _ _))
end ReciprocityTheory.L2DbarEstimates.F
