-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_fibreDiscr_eq_pairProd_4d8cdf3a1f36
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:59.140604+00:00
-- url     : https://prove2.me/submissions/44f774d0-94e8-44c4-838a-8fbdf08f08eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFibreDiscriminantHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreDiscriminantHolomorphic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Metric Set
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
variable {σ : Type} [Fintype σ]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
theorem _root_.solution {Y : Set (σ → ℂ)} {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {N : ℕ}
    (l : (σ → ℂ) →L[ℂ] ℂ) {y : Fin d → ℂ} (hle : {x | x ∈ Y ∧ A x = y}.encard ≤ N)
    {p : Fin N → σ → ℂ} (hp : Function.Injective p) (hpY : ∀ i, p i ∈ Y ∧ A (p i) = y) :
    fibreDiscr Y A l N y = pairProd l p := by
  have hsub : range p ⊆ {x | x ∈ Y ∧ A x = y} := by
    rintro _ ⟨i, rfl⟩
    exact hpY i
  have hr : (range p).encard = N := by
    rw [← image_univ, hp.encard_image, encard_univ]
    simp
  have heq : range p = {x | x ∈ Y ∧ A x = y} :=
    (Set.finite_range p).eq_of_subset_of_encard_le hsub (by rw [hr]; exact hle)
  have hN : {x | x ∈ Y ∧ A x = y}.encard = N := heq ▸ hr
  unfold fibreDiscr
  rw [dif_pos hN]
  unfold pairProd
  symm
  refine Finset.prod_bij (fun q _ => (p q.1, p q.2)) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at hq
    simp only [Finset.mem_offDiag, Set.Finite.mem_toFinset]
    exact ⟨hpY _, hpY _, fun h => hq (hp h)⟩
  · intro a _ b _ hab
    simp only [Prod.mk.injEq] at hab
    exact Prod.ext (hp hab.1) (hp hab.2)
  · intro b hb
    simp only [Finset.mem_offDiag, Set.Finite.mem_toFinset] at hb
    obtain ⟨i, hi⟩ : b.1 ∈ range p := heq ▸ hb.1
    obtain ⟨j, hj⟩ : b.2 ∈ range p := heq ▸ hb.2.1
    refine ⟨(i, j), ?_, ?_⟩
    · simp only [Finset.mem_offDiag, Finset.mem_univ, true_and]
      rintro rfl
      exact hb.2.2 (hi.symm.trans hj)
    · simp [hi, hj]
  · intro q _
    rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
