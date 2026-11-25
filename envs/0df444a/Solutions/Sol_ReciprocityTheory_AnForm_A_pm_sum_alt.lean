-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.pm_sum_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:12:24.487382+00:00
-- url     : https://prove2.me/submissions/d253c624-dcc4-43f3-8da9-55dd11124f05

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Theorems.Thm_ReciprocityTheory_AnForm_A_pm_alt

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
theorem _root_.solution (g : Fin D → Fin D × ι) :
    ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (if ∀ a, (g a).1 ∈ S then 1 else 0) =
      (pmWt g : ℂ) := by
  have h : ∀ S : Finset (Fin D), (∀ a, (g a).1 ∈ S) ↔ univ.image (fun a => (g a).1) ⊆ S := by
    intro S; simp [Finset.image_subset_iff]
  simp only [h, pm_alt, pmWt]
  split_ifs <;> simp
end ReciprocityTheory.AnForm.A
