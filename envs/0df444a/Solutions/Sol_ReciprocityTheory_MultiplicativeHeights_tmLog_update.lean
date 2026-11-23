-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.tmLog_update
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:02.946181+00:00
-- url     : https://prove2.me/submissions/5ad94417-0f76-4fad-ade2-0049b0392325

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_tm_eval_update
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_torusPoint_update


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Real Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (f : MvPolynomial ι ℂ) (θ : ι → ℝ) (i : ι) (t : ℝ) :
    tmLog f (update θ i t) = Real.log ‖(tmSlice i (torusPoint θ) f).eval (circPt t)‖ := by
  rw [tmLog, torusPoint_update, tm_eval_update]
end ReciprocityTheory.MultiplicativeHeights
