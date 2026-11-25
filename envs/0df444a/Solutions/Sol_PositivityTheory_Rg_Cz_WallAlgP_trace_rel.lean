-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.WallAlgP.trace_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:37:19.704616+00:00
-- url     : https://prove2.me/submissions/e128f705-9732-4b7f-a649-975034405ddb

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PWallAlgA
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
import Theorems.Thm_PositivityTheory_Rg_Cz_tE_apply
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
open PositivityTheory.Rg.Cz.WallAlgP
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.WallAlgP
theorem _root_.solution (E₁ E₂ : Fin n → Fin n → Module.End ℂ M) {m : ℕ} (c t₁ t₂ : ℂ) (ξ : TV n M (Fin m))
    (h₁ : ∑ a, E₁ a a = algebraMap ℂ _ t₁) (h₂ : ∑ a, E₂ a a = algebraMap ℂ _ t₂)
    (hX : ∀ a b, tE Finset.univ (fun a b => E₁ a b + E₂ a b) a b ξ = if a = b then c • ξ else 0) :
    (t₁ + t₂ + m) • ξ = ((n : ℂ) * c) • ξ := by
  funext I
  have key : ∑ a, tE Finset.univ (fun a b => E₁ a b + E₂ a b) a a ξ I = ∑ a, (if a = a then c • ξ else 0) I :=
    Finset.sum_congr rfl fun a _ => congrFun (hX a a) _
  simp only [tE_apply, Finset.sum_add_distrib, LinearMap.add_apply, if_true] at key
  rw [Finset.sum_comm] at key
  have h3 : ∀ p : Fin m, ∑ a, (if I p = a then ξ (Function.update I p a) else 0) = ξ I := by
    intro p
    rw [Finset.sum_ite_eq]; simp
  have e₁ : ∑ a, E₁ a a (ξ I) = t₁ • ξ I := by
    rw [← LinearMap.sum_apply, h₁]; rfl
  have e₂ : ∑ a, E₂ a a (ξ I) = t₂ • ξ I := by
    rw [← LinearMap.sum_apply, h₂]; rfl
  rw [Finset.sum_congr rfl fun p _ => h3 p, e₁, e₂] at key
  simp only [Pi.smul_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at key ⊢
  rw [add_smul, add_smul, mul_smul, Nat.cast_smul_eq_nsmul ℂ m, Nat.cast_smul_eq_nsmul ℂ n]
  exact key
end PositivityTheory.Rg.Cz.WallAlgP
