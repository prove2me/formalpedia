-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mdisc_conjTranspose_mul_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:24:34.060897+00:00
-- url     : https://prove2.me/submissions/a1b61f72-d165-4f86-986f-785758b6e1a8

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_mul_mul

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
theorem _root_.solution (P : Matrix (Fin D) (Fin D) ℂ)
    (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mdisc (fun k => Pᴴ * A k * P) = (Complex.normSq P.det : ℂ) * mdisc A := by
  rw [mdisc_mul_mul, Matrix.det_conjTranspose]
  congr 1
  rw [mul_comm]
  exact Complex.mul_conj _
end ReciprocityTheory.AnForm.A
