-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.WallAlgP.coset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:37:04.678828+00:00
-- url     : https://prove2.me/submissions/ed1fc92f-1ecc-4827-bcba-65bb99c00a0b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PWallAlgA
import Theorems.Thm_PositivityTheory_Rg_Cz_WallAlgP_mem_firstG
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
open PositivityTheory.Rg.Cz.WallAlgP
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.WallAlgP
theorem _root_.solution {m k : ℕ} (hk : k < m) {V : Type} [AddCommMonoid V] (f : Equiv.Perm (Fin m) → V) :
    ∑ τ ∈ firstG m (k + 1), f τ = ∑ σ ∈ firstG m k, f σ +
      ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), ∑ σ ∈ firstG m k, f (Equiv.swap j ⟨k, hk⟩ * σ) := by
  set k' : Fin m := ⟨k, hk⟩ with hk'
  have hins : (Finset.univ.filter fun j : Fin m => (j : ℕ) ≤ k) =
      insert k' (Finset.univ.filter fun j : Fin m => (j : ℕ) < k) := by
    ext j; simp [Fin.ext_iff, k']; omega
  have hnot : k' ∉ (Finset.univ.filter fun j : Fin m => (j : ℕ) < k) := by simp [k']
  have h1 : ∑ τ ∈ firstG m (k + 1), f τ = ∑ p ∈ (Finset.univ.filter fun j : Fin m => (j : ℕ) ≤ k) ×ˢ firstG m k,
      f (Equiv.swap p.1 k' * p.2) := by
    refine Finset.sum_nbij' (fun τ => (τ k', Equiv.swap (τ k') k' * τ)) (fun p => Equiv.swap p.1 k' * p.2)
      ?_ ?_ ?_ ?_ ?_
    · intro τ hτ
      rw [mem_firstG] at hτ
      have hle : (τ k' : ℕ) ≤ k := by
        by_contra h
        have h2 := hτ (τ k') (by omega)
        have h3 := τ.injective h2
        rw [h3] at h
        simp [k'] at h
      refine Finset.mem_product.2 ⟨by simpa using hle, ?_⟩
      rw [mem_firstG]
      intro j hj
      rw [Equiv.Perm.mul_apply]
      by_cases hjk : j = k'
      · rw [hjk, Equiv.swap_apply_left]
      · have hj1 : k + 1 ≤ (j : ℕ) := by
          have : (j : ℕ) ≠ k := fun h => hjk (Fin.ext h)
          omega
        rw [hτ j hj1]
        refine Equiv.swap_apply_of_ne_of_ne ?_ hjk
        intro h; rw [h] at hj1; omega
    · intro p hp
      rw [Finset.mem_product] at hp
      obtain ⟨hp1, hp2⟩ := hp
      rw [mem_firstG] at hp2 ⊢
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp1
      intro j hj
      rw [Equiv.Perm.mul_apply, hp2 j (by omega)]
      refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
      · intro h; rw [h] at hj; omega
      · intro h; rw [h] at hj; simp [k'] at hj
    · intro τ _
      simp only [Equiv.swap_mul_self_mul]
    · intro p hp
      rw [Finset.mem_product, mem_firstG] at hp
      have hk2 := hp.2 k' (le_refl _)
      simp only [Equiv.Perm.mul_apply, hk2, Equiv.swap_apply_right, Equiv.swap_mul_self_mul]
    · intro τ _
      simp only [Equiv.swap_mul_self_mul]
  rw [h1, Finset.sum_product, hins, Finset.sum_insert hnot]
  simp only [Equiv.swap_self, ← Equiv.Perm.one_def, one_mul]
end PositivityTheory.Rg.Cz.WallAlgP
