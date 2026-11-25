-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_norm_fibreDiscr_le_b1f5bc30d339
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:32:32.650947+00:00
-- url     : https://prove2.me/submissions/577f4434-306b-416c-aaf7-88a0651b2306

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFibreDiscriminantHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreDiscriminantHolomorphic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_norm_prod_le_pow_309320c6e6da

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
theorem _root_.solution {Y : Set (σ → ℂ)} {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)}
    {K : Set (Fin d → ℂ)} {N : ℕ} (l : (σ → ℂ) →L[ℂ] ℂ) {C : ℝ} (hC : 1 ≤ C)
    (hCb : ∀ a ∈ {x | x ∈ Y ∧ A x ∈ K}, ∀ b ∈ {x | x ∈ Y ∧ A x ∈ K}, ‖l a - l b‖ ≤ C)
    {y : Fin d → ℂ} (hy : y ∈ K) : ‖fibreDiscr Y A l N y‖ ≤ C ^ (N * N) := by
  unfold fibreDiscr
  split_ifs with h
  · have hc : (Set.finite_of_encard_eq_coe h).toFinset.card = N := by
      have := (Set.finite_of_encard_eq_coe h).encard_eq_coe_toFinset_card
      rw [h] at this
      exact_mod_cast this.symm
    apply norm_prod_le_pow _ _ hC
    · rw [Finset.offDiag_card, hc]
      exact Nat.sub_le _ _
    · intro q hq
      rw [Finset.mem_offDiag, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hq
      exact hCb _ ⟨hq.1.1, by rw [hq.1.2]; exact hy⟩ _ ⟨hq.2.1.1, by rw [hq.2.1.2]; exact hy⟩
  · rw [norm_zero]
    exact pow_nonneg (by linarith) _
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
