-- Prove2me | solution 1 for PigeonholeDesign.Upper.lemma_EC_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:28:26.534471+00:00
-- url     : https://prove2.me/submissions/cb50843b-06a1-4b6e-8fb3-a4027a2528ab

import Mathlib
import Definitions.Def_PigeonholeDesign_Upper_Setting
set_option autoImplicit false
open PigeonholeDesign.Upper

lemma phu_disc_perm {T : ℕ} (σ : Equiv.Perm (Fin T)) (x : Fin T → ℝ) (w : Fin T → Bool) :
    discrepancy (x ∘ σ) w = discrepancy x (w ∘ σ.symm) := by
  unfold discrepancy
  let eA : {t // w t = false} ≃ {t // (w ∘ σ.symm) t = false} :=
    σ.subtypeEquiv (fun t => by simp)
  let eB : {t // w t = true} ≃ {t // (w ∘ σ.symm) t = true} :=
    σ.subtypeEquiv (fun t => by simp)
  refine Equiv.iInf_congr (Equiv.equivCongr eA eB) (fun e => ?_)
  rw [← Equiv.sum_comp eA.symm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp [eA, eB, Equiv.equivCongr]

theorem solution {T : ℕ} (σ : Equiv.Perm (Fin T)) (x : Fin T → ℝ) :
    crdExp (x ∘ σ) = crdExp x := by
  unfold crdExp
  congr 1
  simp_rw [phu_disc_perm]
  refine Finset.sum_bij (fun V _ => V.map σ.toEmbedding) ?_ ?_ ?_ ?_
  · intro V hV
    simp only [Finset.mem_powersetCard] at hV ⊢
    exact ⟨Finset.subset_univ _, by simpa using hV.2⟩
  · intro V _ V' _ h
    exact Finset.map_injective _ h
  · intro V hV
    simp only [Finset.mem_powersetCard] at hV
    refine ⟨V.map σ.symm.toEmbedding, ?_, ?_⟩
    · simp only [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, by simpa using hV.2⟩
    · rw [Finset.map_map]
      have : σ.symm.toEmbedding.trans σ.toEmbedding = Function.Embedding.refl _ := by
        ext; simp
      rw [this]; simp
  · intro V hV
    congr 1
    funext t
    simp
