-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.continuous_two_form_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:13:57.715696+00:00
-- url     : https://prove2.me/submissions/9591453f-5b41-44b9-a3e2-279f6ee836ab

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
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
  show Continuous fun σ : Fin n → Fin n → ℂ => sq2 n σ
  simp only [sq2]
  first
  | fun_prop
  | exact (continuous_finset_sum _ fun j _ => continuous_finset_sum _ fun k _ =>
      ((continuous_apply k).comp (continuous_apply j)).norm.pow 2).div_const _
end ReciprocityTheory.L2DbarEstimates.F
