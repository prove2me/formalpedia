-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.measurableSet_zeroTorus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:25:52.848856+00:00
-- url     : https://prove2.me/submissions/f436efae-485c-47c4-832e-76b22eee877c

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_continuous_eval_torus


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
theorem _root_.solution (f : MvPolynomial ι ℂ) :
    MeasurableSet {θ : ι → ℝ | MvPolynomial.eval (torusPoint θ) f = 0} :=
  (continuous_eval_torus f).measurable (measurableSet_singleton 0)
end ReciprocityTheory.MultiplicativeHeights
