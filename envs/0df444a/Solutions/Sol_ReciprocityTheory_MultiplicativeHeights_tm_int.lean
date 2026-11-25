-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.tm_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:25:16.688514+00:00
-- url     : https://prove2.me/submissions/c366b575-cf53-4e71-94fa-b6830c48aa35

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanC
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanD
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integrable_log_abs_on_torus

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
theorem _root_.solution (f : MvPolynomial ι ℂ) : Integrable (tmLog f) (torusProb ι) :=
  integrable_log_abs_on_torus Finset.univ f (Finset.subset_univ _)
end ReciprocityTheory.MultiplicativeHeights
