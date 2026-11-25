-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mixedDiscriminant_nonneg_of_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:49:59.629807+00:00
-- url     : https://prove2.me/submissions/8375d1ec-0791-4684-8d7e-a759802e02b1

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Theorems.Thm_ReciprocityTheory_AnForm_A_pm_mdisc_gram_sum_nonneg
import Theorems.Thm_ReciprocityTheory_AnForm_A_pm_exists_gram_of_posSemidef
import Theorems.Thm_ReciprocityTheory_AnForm_A_pm_mdisc_of_gram

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
theorem _root_.solution (A : Fin D → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ k, (A k).PosSemidef) : (mdisc A).im = 0 ∧ 0 ≤ (mdisc A).re := by
  choose v hv using fun k => pm_exists_gram_of_posSemidef (hA k)
  rw [pm_mdisc_of_gram A v hv]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  exact div_nonneg (pm_mdisc_gram_sum_nonneg _) (by positivity)
end ReciprocityTheory.AnForm.A
