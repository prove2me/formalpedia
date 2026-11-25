-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mdisc_pos_of_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:57:43.871002+00:00
-- url     : https://prove2.me/submissions/9802cb43-c543-4973-9cba-047b5ee5adf3

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Theorems.Thm_ReciprocityTheory_AnForm_A_mixedDiscriminant_pos_of_gram


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
    (hA : ∀ k, (A k).PosDef) : (mdisc A).im = 0 ∧ 0 < (mdisc A).re := by
  exact mixedDiscriminant_pos_of_gram A hA
end ReciprocityTheory.AnForm.A
