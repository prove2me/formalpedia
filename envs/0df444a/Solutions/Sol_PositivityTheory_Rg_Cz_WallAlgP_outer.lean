-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.WallAlgP.outer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:44:23.676797+00:00
-- url     : https://prove2.me/submissions/0f2d365e-a2e3-4666-8a9a-26a8efee2046

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PWallAlgA
import Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_mem_firstG
import Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_coset
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_mul
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
open PositivityTheory.Rg.Cz.WallAlgP
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.WallAlgP
theorem _root_.solution {m k : ℕ} (hk : k < m) (X : Submodule ℂ (TV n M (Fin m))) (hP : ∀ σ, ∀ ξ ∈ X, pm σ ξ ∈ X)
    (h0 : ∀ ξ ∈ X, alt (firstG m (k + 1)) ξ = 0) (ξ) (hξ : ξ ∈ X) (i : Fin m) (hi : k ≤ (i : ℕ)) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), pm (Equiv.swap j i) (alt (firstG m k) ξ) =
      alt (firstG m k) ξ := by
  set k' : Fin m := ⟨k, hk⟩ with hk'
  set π := Equiv.swap k' i with hπ
  have hπ2 : π * π = 1 := Equiv.swap_mul_self k' i
  have hcomm : ∀ η : TV n M (Fin m), alt (firstG m k) (pm π η) = pm π (alt (firstG m k) η) := by
    intro η
    simp only [alt, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [mem_firstG] at hσ
    congr 1
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pm_mul, ← pm_mul]
    congr 1
    rw [hπ, Equiv.mul_swap_eq_swap_mul, hσ k' (le_refl _), hσ i hi]
  have hdec : ∀ η : TV n M (Fin m), alt (firstG m (k + 1)) η = alt (firstG m k) η -
      ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), pm (Equiv.swap j k') (alt (firstG m k) η) := by
    intro η
    have hc := coset hk (fun τ => ((Equiv.Perm.sign τ : ℤ) : ℂ) • pm τ η)
    simp only at hc
    simp only [alt, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [hc, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hne : j ≠ k' := by
      intro h; rw [h] at hj; simp [k'] at hj
    rw [map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne, pm_mul, map_smul, Module.End.mul_apply]
    simp
    rfl
  have hA := h0 (pm π ξ) (hP π ξ hξ)
  rw [hdec, hcomm, sub_eq_zero] at hA
  have h2 := congrArg (pm π) hA
  rw [← Module.End.mul_apply, ← pm_mul, hπ2, pm_one, Module.End.one_apply, map_sum] at h2
  conv_rhs => rw [h2]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  have hj1 : π j = j := by
    refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
    · intro h; rw [h] at hj; simp [k'] at hj
    · intro h; rw [h] at hj; omega
  have e : Equiv.swap j i = π * Equiv.swap j k' * π := by
    rw [Equiv.mul_swap_eq_swap_mul π j k', hj1, hπ, Equiv.swap_apply_left, mul_assoc, ← hπ, hπ2, mul_one]
  rw [e]
  simp only [pm_mul, Module.End.mul_apply]
end PositivityTheory.Rg.Cz.WallAlgP
