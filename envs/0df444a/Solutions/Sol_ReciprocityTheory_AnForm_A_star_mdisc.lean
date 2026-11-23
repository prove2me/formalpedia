-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.star_mdisc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:11.777355+00:00
-- url     : https://prove2.me/submissions/f5af4c55-b269-4fb7-9301-37e4e001b007

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt

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
theorem _root_.solution (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    star (mdisc A) = mdisc (fun k => (A k)ᴴ) := by
  simp only [mdisc, star_mul', star_sum, ← Matrix.conjTranspose_sum, Matrix.det_conjTranspose,
    star_pow, star_neg, star_one, star_div₀, star_natCast]
end ReciprocityTheory.AnForm.A
