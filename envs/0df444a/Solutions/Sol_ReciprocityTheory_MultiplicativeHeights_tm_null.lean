-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.tm_null
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:17:40.812818+00:00
-- url     : https://prove2.me/submissions/1e63d088-06ec-482e-98b8-b58093b1c9a7

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_torus_zero_set_measure_zero

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
theorem _root_.solution (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    torusProb ι {θ | MvPolynomial.eval (torusPoint θ) f = 0} = 0 :=
  torus_zero_set_measure_zero Finset.univ f (Finset.subset_univ _) hf
end ReciprocityTheory.MultiplicativeHeights
