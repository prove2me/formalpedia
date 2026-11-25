-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:57:08.416487+00:00
-- url     : https://prove2.me/submissions/19429d8d-0baf-4038-924a-61a5f5dd43d0

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
theorem _root_.solution (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (hφ : ∀ k, (hessC (φ k) z).PosSemidef) : 0 ≤ maDens φ z := by
  unfold maDens
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg (div_nonneg zero_le_two Real.pi_pos.le) _))
    (mixedDiscriminant_nonneg_of_gram _ hφ).2
end ReciprocityTheory.AnForm.A
