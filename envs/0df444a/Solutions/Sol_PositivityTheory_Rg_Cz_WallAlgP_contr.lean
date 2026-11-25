-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.WallAlgP.contr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:36:46.490914+00:00
-- url     : https://prove2.me/submissions/f38588ce-38bc-485f-8396-fe85d1c5edb9

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PWallAlgA
import Theorems.Thm_PositivityTheory_Rg_Cz_Om_apply
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
theorem _root_.solution (E₁ E₂ : Fin n → Fin n → Module.End ℂ M) {m : ℕ} (c : ℂ) (ξ : TV n M (Fin m))
    (hX : ∀ a b, tE Finset.univ (fun a b => E₁ a b + E₂ a b) a b ξ = if a = b then c • ξ else 0) (j : Fin m) :
    Om E₁ j ξ + Om E₂ j ξ + ∑ p ∈ Finset.univ.filter (· ≠ j), pm (Equiv.swap j p) ξ + (n : ℂ) • ξ = c • ξ := by
  funext I
  have key : ∑ a, tE Finset.univ (fun a b => E₁ a b + E₂ a b) a (I j) ξ (Function.update I j a) =
      ∑ a, (if a = I j then c • ξ else 0) (Function.update I j a) :=
    Finset.sum_congr rfl fun a _ => congrFun (hX a (I j)) _
  have hR : ∑ a, (if a = I j then c • ξ else 0) (Function.update I j a) = c • ξ I := by
    simp only [ite_apply, Pi.smul_apply, Pi.zero_apply]
    rw [Finset.sum_ite_eq']
    simp
  simp only [tE_apply, Finset.sum_add_distrib, LinearMap.add_apply] at key
  rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at key
  have h1 : ∑ a, (if Function.update I j a j = a then
      ξ (Function.update (Function.update I j a) j (I j)) else 0) = (n : ℂ) • ξ I := by
    simp [Function.update_idem]
    exact (Nat.cast_smul_eq_nsmul ℂ n _).symm
  have h2 : ∀ p ∈ Finset.univ.erase j, ∑ a, (if Function.update I j a p = a then
      ξ (Function.update (Function.update I j a) p (I j)) else 0) = ξ (I ∘ Equiv.swap j p) := by
    intro p hp
    have hpj : p ≠ j := Finset.ne_of_mem_erase hp
    simp only [Function.update_of_ne hpj]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    congr 1
    funext x
    simp only [Function.comp_apply, Function.update_apply, Equiv.swap_apply_def]
    split_ifs <;> subst_vars <;> simp_all
  rw [h1, Finset.sum_congr rfl h2, hR] at key
  simp only [Pi.add_apply, Pi.smul_apply, Om_apply, Finset.sum_apply, pm_apply, Finset.filter_ne']
  rw [← key]
  abel
end PositivityTheory.Rg.Cz.WallAlgP
