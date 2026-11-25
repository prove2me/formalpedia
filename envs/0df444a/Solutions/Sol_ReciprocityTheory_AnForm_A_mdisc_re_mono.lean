-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mdisc_re_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:57:25.616151+00:00
-- url     : https://prove2.me/submissions/df1fc8e0-89b4-4416-8680-b03a6366c33d

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Theorems.Thm_ReciprocityTheory_AnForm_A_mixedDiscriminant_re_mono_of_gram


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
theorem _root_.solution (A B : Fin D → Matrix (Fin D) (Fin D) ℂ) (hA : ∀ k, (A k).PosSemidef)
    (hAB : ∀ k, (B k - A k).PosSemidef) : (mdisc A).re ≤ (mdisc B).re := by
  exact mixedDiscriminant_re_mono_of_gram A B hA hAB
end ReciprocityTheory.AnForm.A
