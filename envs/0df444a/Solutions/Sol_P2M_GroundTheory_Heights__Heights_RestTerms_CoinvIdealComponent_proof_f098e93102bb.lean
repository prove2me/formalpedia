-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CoinvIdealComponent_proof_f098e93102bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:53:54.157504+00:00
-- url     : https://prove2.me/submissions/18b273cb-1aad-4c2d-ba23-86df3cf62ae8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvIdealComponent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_bps_isHomogeneous_ce8782615597

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset Coinv
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace CoinvIdealComponent
theorem _root_.solution (h1 : CoinvIdealRepresentation.Statement)
    (h2 : HomogeneousComponentMul.Statement) : CoinvIdealComponent.Statement := by
  intro K _ f n J hJ d
  obtain ⟨a, rfl⟩ := h1 K f n J hJ
  refine ⟨fun m b => if m ≤ d then homogeneousComponent (d - m) (a m b) else 0, ?_, ?_⟩
  · intro m b
    dsimp only
    split_ifs
    · exact homogeneousComponent_isHomogeneous _ _
    · exact isHomogeneous_zero _ _ _
  · rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [h2 (Fin f × Fin n) K (bps K f n m b) (a m b) m d (bps_isHomogeneous K f n m b)]
    by_cases hmd : m ≤ d <;> simp [hmd]
end CoinvIdealComponent
end GroundTheory.Heights₂.Heights.RestTerms
