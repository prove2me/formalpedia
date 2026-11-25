-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.HeightVanishing.prod_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:01:49.530794+00:00
-- url     : https://prove2.me/submissions/46c34eb1-2615-4635-8a31-ae053d2acbb8

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PHeight
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_letter_zero
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_vanish
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_eval
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_prod_deg
import Theorems.Thm_PositivityTheory_Rg_Cz_Om_apply
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
namespace PositivityTheory.Rg.Cz.HeightVanishing
theorem _root_.solution {ℓ : M →ₗ[ℂ] ℂ} {ψ : Fin n → Fin n → ℂ} (hE : GlRel E)
    (hψ1 : ∀ a b : Fin n, (a : ℕ) + 1 = b → ψ a b ≠ 0)
    (hψ2 : ∀ a b : Fin n, (a : ℕ) + 1 < b → ψ a b = 0) (hψ : ∀ a b : Fin n, a < b → ℓ ∘ₗ E a b = ψ a b • ℓ)
    (L : List ℂ) : ∀ j i : Fin n, (j : ℕ) + L.length = i → ∃ c : ℂ, c ≠ 0 ∧ ∀ v,
      ℓ ((L.map fun r => Om E (0 : Fin 1) - algebraMap ℂ _ r).prod (Pi.single (fun _ => j) v) (fun _ => i)) =
        c * ℓ v := by
  have hl : ∀ (b c : Fin n) (X : M), b < c → ℓ (E b c X) = ψ b c * ℓ X := fun b c X hbc => by
    rw [← LinearMap.comp_apply, hψ b c hbc]; rfl
  have hu : ∀ b : Fin n, Function.update (fun _ : Fin 1 => b) 0 = fun c => (fun _ : Fin 1 => c) := by
    intro b; funext c x; rw [Subsingleton.elim x 0]; simp
  induction L with
  | nil =>
    intro j i hji
    have : j = i := Fin.ext (by simpa using hji)
    subst this
    exact ⟨1, one_ne_zero, fun v => by simp⟩
  | cons r L ih =>
    intro j i hji
    simp only [List.length_cons] at hji
    obtain ⟨hdeg, -⟩ := prod_deg E L
    set a : Fin n := ⟨(i : ℕ) - 1, by omega⟩ with ha
    obtain ⟨c, hc, hcv⟩ := ih j a (by simp only [a]; omega)
    refine ⟨ψ a i * c, mul_ne_zero (hψ1 a i (by simp only [a]; omega)) hc, fun v => ?_⟩
    simp only [List.map_cons, List.prod_cons]
    rw [Module.End.mul_apply, LinearMap.sub_apply, Pi.sub_apply, map_sub]
    obtain ⟨B, hB, hBv⟩ := eval E hdeg (fun _ => i) (fun _ => j)
    have h2 : ℓ (algebraMap ℂ (Module.End ℂ (TV n M (Fin 1))) r ((L.map fun r => Om E (0 : Fin 1) - algebraMap ℂ _ r).prod
        (Pi.single (fun _ => j) v)) (fun _ => i)) = 0 := by
      rw [Module.algebraMap_end_apply, Pi.smul_apply, hBv, map_smul, ← LinearMap.comp_apply,
        vanish E hE hψ2 hψ L.length _ B hB (by simp [H]; omega)]
      simp
    rw [h2, sub_zero, Om_apply, map_sum, hu]
    rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _) ?_]
    · rw [hl a i _ (Fin.lt_def.2 (by simp only [a]; omega)), hcv]; ring
    · intro a' _ ha'
      rcases lt_or_ge a' i with h3 | h3
      · have h3' := Fin.lt_def.1 h3
        have h4 : (a' : ℕ) + 1 < i := by
          rcases (show (a' : ℕ) + 1 < i ∨ (a' : ℕ) = (i : ℕ) - 1 by omega) with h | h
          · exact h
          · exact absurd (Fin.ext (by simp only [a]; omega)) ha'
        rw [hl a' i _ h3, hψ2 a' i h4, zero_mul]
      · have h3' := Fin.le_def.1 h3
        obtain ⟨B', hB', hB'v⟩ := eval E hdeg (fun _ => a') (fun _ => j)
        rw [hB'v, ← Module.End.mul_apply, ← LinearMap.comp_apply,
          letter_zero E hE hψ2 hψ (vanish E hE hψ2 hψ L.length) a' i (by push_cast; omega) hB'
            (by simp [H]; omega)]
        rfl
end PositivityTheory.Rg.Cz.HeightVanishing
