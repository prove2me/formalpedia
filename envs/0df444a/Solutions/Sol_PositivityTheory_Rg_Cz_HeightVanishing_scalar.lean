-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.HeightVanishing.scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:59:05.455001+00:00
-- url     : https://prove2.me/submissions/d3e0b487-445e-447e-8965-78bb578de9c9

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PHeight
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_ht_cons
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_word_cons
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_word_mem
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_W_ind
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_letter_zero
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_vanish
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.HeightVanishing
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable (E : Fin n → Fin n → Module.End ℂ M)
variable {ℓ : M →ₗ[ℂ] ℂ} {ψ : Fin n → Fin n → ℂ} (hE : GlRel E)
  (hψ2 : ∀ a b : Fin n, (a : ℕ) + 1 < b → ψ a b = 0) (hψ : ∀ a b : Fin n, a < b → ℓ ∘ₗ E a b = ψ a b • ℓ)
include hE hψ2 hψ
namespace PositivityTheory.Rg.Cz.HeightVanishing
theorem _root_.solution (d : ℕ) : ∀ A : Module.End ℂ M, A ∈ W E d d → ∃ c : ℂ, ℓ ∘ₗ A = c • ℓ := by
  induction d with
  | zero =>
    intro A hA
    refine W_ind E (p := fun A => ∃ c : ℂ, ℓ ∘ₗ A = c • ℓ) ⟨0, by simp⟩ ?_ ?_ ?_ hA
    · rintro x y ⟨c, hc⟩ ⟨c', hc'⟩; exact ⟨c + c', by rw [LinearMap.comp_add, hc, hc', add_smul]⟩
    · rintro c x ⟨c', hc'⟩; exact ⟨c * c', by rw [LinearMap.comp_smul, hc', smul_smul]⟩
    · intro w h1 h2
      have : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      exact ⟨1, by simp only [word, List.map_nil, List.prod_nil, one_smul]; exact LinearMap.comp_id ℓ⟩
  | succ d ih =>
    intro A hA
    refine W_ind E (p := fun A => ∃ c : ℂ, ℓ ∘ₗ A = c • ℓ) ⟨0, by simp⟩ ?_ ?_ ?_ hA
    · rintro x y ⟨c, hc⟩ ⟨c', hc'⟩; exact ⟨c + c', by rw [LinearMap.comp_add, hc, hc', add_smul]⟩
    · rintro c x ⟨c', hc'⟩; exact ⟨c * c', by rw [LinearMap.comp_smul, hc', smul_smul]⟩
    · intro w h1 h2
      cases w with
      | nil => simp [ht] at h2; omega
      | cons x w =>
        obtain ⟨a, b⟩ := x
        rw [ht_cons] at h2
        simp only [List.length_cons] at h1
        rw [word_cons]
        rcases lt_or_ge a b with hab | hab
        · have hab' := Fin.lt_def.1 hab
          rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hψ a b hab]
          rcases (show (a : ℕ) + 1 = b ∨ (a : ℕ) + 1 < b by omega) with h3 | h3
          · obtain ⟨c, hc⟩ := ih _ (word_mem E w (by omega) (by push_cast at h2; omega))
            exact ⟨ψ a b * c, by rw [LinearMap.smul_comp, hc, smul_smul]⟩
          · exact ⟨0, by rw [hψ2 a b h3]; simp⟩
        · have hab' := Fin.le_def.1 hab
          exact ⟨0, by rw [letter_zero E hE hψ2 hψ (vanish E hE hψ2 hψ d) a b (by push_cast; omega)
            (word_mem E w (by omega) rfl) (by push_cast at h2 ⊢; omega), zero_smul]⟩
end PositivityTheory.Rg.Cz.HeightVanishing
