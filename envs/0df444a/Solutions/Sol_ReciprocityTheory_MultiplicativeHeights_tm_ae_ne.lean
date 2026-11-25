-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.tm_ae_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:28:14.474117+00:00
-- url     : https://prove2.me/submissions/d359ce27-d212-48f5-b774-637a3a1be327

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanC
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanD
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_tm_null


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
    ∀ᵐ θ ∂(torusProb ι), MvPolynomial.eval (torusPoint θ) f ≠ 0 := by
  rw [ae_iff]; simpa using tm_null f hf
end ReciprocityTheory.MultiplicativeHeights
