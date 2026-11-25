-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.pm_mdisc_gram_sum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:06:48.36566+00:00
-- url     : https://prove2.me/submissions/038fb62a-b432-468d-9930-2a2fb535909b

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Theorems.Thm_ReciprocityTheory_AnForm_A_pmWt_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix Finset
open scoped ComplexOrder
variable {D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (w : Fin D → ι → Fin D → ℂ) :
    0 ≤ ∑ g : Fin D → Fin D × ι, pmWt g * Complex.normSq (pmGmat w g).det :=
  Finset.sum_nonneg fun g _ => mul_nonneg (pmWt_nonneg g) (Complex.normSq_nonneg _)
end ReciprocityTheory.AnForm.A
