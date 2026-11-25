-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Elem_sum_primeWeight_le_932b2b356f63
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:06:34.119817+00:00
-- url     : https://prove2.me/submissions/e45dd877-09eb-4a7b-967b-ba8c2c69b152

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PrimeWeightEqZeroOfLt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_ChebyshevThetaBound_intersectionNumber_baseChange_1e58a3fff588
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_ExponentialTail_intersectionNumber_baseChange_69f6990adeee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_GeometricTail_intersectionNumber_baseChange_cf5b94796824
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_RestConstants_intersectionNumber_baseChange_3cbe9c9bc2bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SmallRankBound_intersectionNumber_baseChange_63d64eced049
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SmallRankWeakHypothesis_intersectionNumber_baseChange_46cb8718a615
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_XBound_intersectionNumber_baseChange_3674cb61fc35
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_XOverPrime_intersectionNumber_baseChange_8ed2297f9f86


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.Elem
namespace GroundTheory.Heights₂.Heights.RestTerms.Elem
theorem _root_.solution (B : ℝ) (K : ℕ) :
    ∑ i ∈ range (K + 1), primeWeight B i ≤ K * Real.log 4 := by
  have hθ := ChebyshevThetaBound.intersectionNumber_baseChange (K : ℝ) (Nat.cast_nonneg K)
  rw [Nat.floor_natCast] at hθ
  refine le_trans ?_ hθ
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i _
  unfold primeWeight
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd h1.1 h2
  · exact Real.log_natCast_nonneg i
  · exact le_rfl
end GroundTheory.Heights₂.Heights.RestTerms.Elem
