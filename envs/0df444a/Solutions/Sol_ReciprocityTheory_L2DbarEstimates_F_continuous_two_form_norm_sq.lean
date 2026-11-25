-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.continuous_two_form_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:10:08.429121+00:00
-- url     : https://prove2.me/submissions/ae22e39f-7560-4016-8c31-111147d8f8e7

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp


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
theorem _root_.solution (n : ℕ) : Continuous (sq2 n) := by
  show Continuous (fun σ : Fin n → Fin n → ℂ => (∑ j, ∑ k, ‖σ j k‖ ^ 2) / 2)
  first
  | fun_prop
  | exact (continuous_finset_sum _ fun j _ => continuous_finset_sum _ fun k _ =>
      (((continuous_apply k).comp (continuous_apply j)).norm.pow 2)).div_const 2
end ReciprocityTheory.L2DbarEstimates.F
