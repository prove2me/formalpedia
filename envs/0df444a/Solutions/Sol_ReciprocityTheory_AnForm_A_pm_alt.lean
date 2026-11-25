-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.pm_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:05:47.453398+00:00
-- url     : https://prove2.me/submissions/93d56472-bcce-46de-b375-0f21b34d21ea

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos

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
theorem _root_.solution (K : Finset (Fin D)) :
    ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (if K ⊆ S then 1 else 0) =
      if K = univ then 1 else 0 := by
  have hc : ∀ T : Finset (Fin D), D - (D - T.card) = T.card := fun T =>
    Nat.sub_sub_self (by simpa using Finset.card_le_univ T)
  rw [← Fintype.sum_bijective (Compl.compl : Finset (Fin D) → Finset (Fin D)) compl_involutive.bijective
    (fun T : Finset (Fin D) => (-1 : ℂ) ^ T.card * if T ⊆ Kᶜ then 1 else 0) _ fun T => by
      simp only [Finset.card_compl, Fintype.card_fin, hc, Finset.subset_compl_comm]]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hf : (univ.filter fun T : Finset (Fin D) => T ⊆ Kᶜ) = Kᶜ.powerset := by ext; simp
  rw [hf]
  have h := Finset.sum_powerset_neg_one_pow_card (x := Kᶜ)
  have h2 := congrArg (Int.cast : ℤ → ℂ) h
  push_cast at h2
  rw [h2]
  simp [Finset.compl_eq_empty_iff]
end ReciprocityTheory.AnForm.A
