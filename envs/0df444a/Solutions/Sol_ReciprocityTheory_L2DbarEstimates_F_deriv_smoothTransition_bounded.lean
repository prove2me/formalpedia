-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.deriv_smoothTransition_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:38.00264+00:00
-- url     : https://prove2.me/submissions/3c300e1d-dc50-47e3-bfd4-a9275e75cdec

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_DerivSmoothTransitionOfOneLt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_deriv_smoothTransition_of_neg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_deriv_smoothTransition_of_one_lt

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
theorem _root_.solution : ∃ C : ℝ, ∀ t, |deriv Real.smoothTransition t| ≤ C := by
  have hd : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hd.continuousOn
  refine ⟨C, fun t => ?_⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, zero_le_one⟩)
  rcases lt_or_ge t 0 with ht | ht
  · rw [deriv_smoothTransition_of_neg ht]; simpa using hC0
  rcases lt_or_ge 1 t with ht' | ht'
  · rw [deriv_smoothTransition_of_one_lt ht']; simpa using hC0
  · simpa [Real.norm_eq_abs] using hC t ⟨ht, ht'⟩
end ReciprocityTheory.L2DbarEstimates.F
