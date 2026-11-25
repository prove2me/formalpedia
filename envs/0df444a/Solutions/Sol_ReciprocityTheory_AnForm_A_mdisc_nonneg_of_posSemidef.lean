-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mdisc_nonneg_of_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:57:14.620138+00:00
-- url     : https://prove2.me/submissions/a0142c42-02ca-4bc6-9e00-e4f1d80de5a2

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Theorems.Thm_ReciprocityTheory_AnForm_A_mixedDiscriminant_nonneg_of_gram


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
    (hA : ∀ k, (A k).PosSemidef) : (mdisc A).im = 0 ∧ 0 ≤ (mdisc A).re := by
  exact mixedDiscriminant_nonneg_of_gram A hA
end ReciprocityTheory.AnForm.A
