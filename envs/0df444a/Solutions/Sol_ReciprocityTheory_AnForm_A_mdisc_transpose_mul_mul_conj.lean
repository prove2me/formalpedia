-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mdisc_transpose_mul_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:40.198955+00:00
-- url     : https://prove2.me/submissions/c9094136-b277-418b-a7ee-b13cd779f31d

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
theorem _root_.solution (J : Matrix (Fin D) (Fin D) ℂ)
    (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mdisc (fun k => Jᵀ * A k * J.map (starRingEnd ℂ)) = (Complex.normSq J.det : ℂ) * mdisc A := by
  rw [mdisc_mul_mul, Matrix.det_transpose,
    show (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det from (RingHom.map_det _ _).symm]
  congr 1
  exact Complex.mul_conj _
end ReciprocityTheory.AnForm.A
