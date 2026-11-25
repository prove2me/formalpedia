-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.HeightVanishing.vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:44.873459+00:00
-- url     : https://prove2.me/submissions/4c8f6c69-7fa1-48be-b92a-c8f7c9864273

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PHeight
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_ht_cons
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_word_cons
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_word_mem
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_W_ind
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_letter_zero
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
theorem _root_.solution (k : ℕ) : ∀ (h : ℤ) (A : Module.End ℂ M), A ∈ W E k h → (k : ℤ) < h → ℓ ∘ₗ A = 0 := by
  induction k with
  | zero =>
    intro h A hA hk
    refine W_ind E (p := fun A => ℓ ∘ₗ A = 0) (by simp)
      (fun x y hx hy => by rw [LinearMap.comp_add, hx, hy, add_zero])
      (fun c x hx => by rw [LinearMap.comp_smul, hx, smul_zero]) ?_ hA
    intro w h1 h2
    have : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [ht] at h2; omega
  | succ k ih =>
    intro h A hA hk
    refine W_ind E (p := fun A => ℓ ∘ₗ A = 0) (by simp)
      (fun x y hx hy => by rw [LinearMap.comp_add, hx, hy, add_zero])
      (fun c x hx => by rw [LinearMap.comp_smul, hx, smul_zero]) ?_ hA
    intro w h1 h2
    cases w with
    | nil => simp [ht] at h2; omega
    | cons x w =>
      obtain ⟨a, b⟩ := x
      rw [ht_cons] at h2
      simp only [List.length_cons] at h1
      rw [word_cons]
      have hw : word E w ∈ W E k (ht w) := word_mem E w (by omega) rfl
      rcases lt_or_ge a b with hab | hab
      · have hab' := Fin.lt_def.1 hab
        rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hψ a b hab]
        rcases (show (a : ℕ) + 1 = b ∨ (a : ℕ) + 1 < b by omega) with h3 | h3
        · rw [LinearMap.smul_comp, ih _ _ hw (by push_cast at hk h2 ⊢; omega), smul_zero]
        · rw [hψ2 a b h3, zero_smul, LinearMap.zero_comp]
      · have hab' := Fin.le_def.1 hab
        exact letter_zero E hE hψ2 hψ ih a b (by push_cast; omega) hw (by push_cast at hk h2 ⊢; omega)
end PositivityTheory.Rg.Cz.HeightVanishing
