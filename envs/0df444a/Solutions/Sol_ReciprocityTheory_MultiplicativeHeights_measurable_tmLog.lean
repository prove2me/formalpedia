-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.measurable_tmLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:56:57.580019+00:00
-- url     : https://prove2.me/submissions/dbff202c-0c5f-41bf-a58a-e1ec9381d585

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_measurable_logEval


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
theorem _root_.solution (f : MvPolynomial ι ℂ) : Measurable (tmLog f) := measurable_logEval f
end ReciprocityTheory.MultiplicativeHeights
