-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mdisc_im_eq_zero_of_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:24:41.487944+00:00
-- url     : https://prove2.me/submissions/41a3fa16-7678-4be2-b6a6-07d1e6428f75

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Theorems.Thm_ReciprocityTheory_AnForm_A_star_mdisc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix
open scoped ComplexOrder
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (A : Fin D → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ k, (A k).IsHermitian) : (mdisc A).im = 0 := by
  have h := star_mdisc A
  have e : (fun k => (A k)ᴴ) = A := funext fun k => (hA k).eq
  rw [e] at h
  exact Complex.conj_eq_iff_im.1 h
end ReciprocityTheory.AnForm.A
