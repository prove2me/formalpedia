-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_weight_mapDomain_midVar_b2a63a3b761b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:24:43.080472+00:00
-- url     : https://prove2.me/submissions/48330bc3-4a52-4944-ae07-cd1a2f38b9d0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinVertDivRight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_midVar_injective_8c0827b6a547
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_weight_blockWeight_apply_e42af7815746


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal mcMap joinCoord midDeg midVar)
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorRight
variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}
variable [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorRight
theorem _root_.solution [DecidableEq K] [DecidableEq K'] [DecidableEq K₂]
    (d : (Σ k : K ⊕ K', Sum.elim ι ι' k) →₀ ℕ) :
    Finsupp.weight (blockWeight (Sum.elim ι (Sum.elim ι₂ ι'))) (Finsupp.mapDomain (midVar ι₂) d) =
      midNat (Finsupp.weight (blockWeight (Sum.elim ι ι')) d) := by
  funext l
  rw [Objects.weight_blockWeight_apply]
  rcases l with k | k | k
  · change _ = Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inl k)
    rw [Objects.weight_blockWeight_apply]
    exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_apply midVar_injective d ⟨.inl k, i⟩
  · change _ = 0
    refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨⟨k' | k', j⟩, h⟩ <;> dsimp only [midVar] at h <;> cases h
  · change _ = Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inr k)
    rw [Objects.weight_blockWeight_apply]
    exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_apply midVar_injective d ⟨.inr k, i⟩
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorRight
