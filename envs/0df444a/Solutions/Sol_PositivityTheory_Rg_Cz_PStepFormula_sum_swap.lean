-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.PStepFormula.sum_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:37:39.569143+00:00
-- url     : https://prove2.me/submissions/67d2c63e-642e-415a-baef-8b27943fddd7

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepFormulaA
import Theorems.Thm_P2M_PositivityTheory_Rg_Cz_PStepFormula_eq_zero_of_eq_neg__68e78d2cc559
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
open PositivityTheory.Rg.Cz.PStepFormula
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.PStepFormula
theorem _root_.solution {X : Type} [AddCommGroup X] [Module ℂ X] (h : (Fin n → Fin n) → (Fin 1 → Fin n) → X)
    (hanti : ∀ J a b, a ≠ b → h (J ∘ Equiv.swap a b) = -h J) (J : Fin n → Fin n) (I : Fin 1 → Fin n) :
    ∑ j, h (Function.update J j (I 0)) (Function.update I 0 (J j)) = h J I := by
  classical
  have hz : ∀ K : Fin n → Fin n, ∀ a b, a ≠ b → K a = K b → h K = 0 := by
    intro K a b hab hK
    have hc : K ∘ Equiv.swap a b = K := by
      funext x
      simp only [Function.comp_apply, Equiv.swap_apply_def]
      split_ifs with h1 h2
      · rw [h1, hK]
      · rw [h2, hK]
      · rfl
    have := hanti K a b hab
    rw [hc] at this
    funext I
    exact eq_zero_of_eq_neg' (congrFun this I)
  by_cases hJ : Function.Injective J
  · obtain ⟨p, hp⟩ := (Finite.injective_iff_surjective.mp hJ) (I 0)
    rw [Finset.sum_eq_single p]
    · rw [← hp, Function.update_eq_self, hp, Function.update_eq_self]
    · intro j _ hj
      rw [hz (Function.update J j (I 0)) j p hj (by simp [Function.update_of_ne (Ne.symm hj), hp]), Pi.zero_apply]
    · simp
  · obtain ⟨a, b, hab, hne⟩ : ∃ a b, J a = J b ∧ a ≠ b := by
      simp only [Function.Injective, not_forall] at hJ
      obtain ⟨a, b, h1, h2⟩ := hJ
      exact ⟨a, b, h1, h2⟩
    rw [hz J a b hne hab, Pi.zero_apply, Fintype.sum_eq_add a b hne]
    · have hc : Function.update J b (I 0) = Function.update J a (I 0) ∘ Equiv.swap a b := by
        funext x
        simp only [Function.comp_apply, Equiv.swap_apply_def]
        by_cases h1 : x = a
        · subst h1
          rw [if_pos rfl, Function.update_of_ne hne, Function.update_of_ne (Ne.symm hne), hab]
        · rw [if_neg h1]
          by_cases h2 : x = b
          · subst h2
            rw [if_pos rfl, Function.update_self, Function.update_self]
          · rw [if_neg h2, Function.update_of_ne h2, Function.update_of_ne h1]
      rw [hc, hanti _ a b hne, hab]
      simp
    · rintro c ⟨hca, hcb⟩
      rw [hz _ a b hne (by simp [Function.update_of_ne (Ne.symm hca), Function.update_of_ne (Ne.symm hcb), hab]),
        Pi.zero_apply]
end PositivityTheory.Rg.Cz.PStepFormula
