-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_RestKSumBound_proof_9adcdb06a5ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:54:08.604827+00:00
-- url     : https://prove2.me/submissions/ae09dd30-56fc-4137-8e14-bad41a2f3aae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsElem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PRestKSumBound
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
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace RestKSumBound
theorem _root_.solution : RestKSumBound.Statement := by
  intro p X N hp hX hXp
  obtain ⟨hsum, htsum, hexp⟩ := ExponentialTail.intersectionNumber_baseChange p X hp hX hXp
  set g : ℕ → ℝ := fun j => 2 * (p ^ (j + 2))⁻¹ * X ^ (j + 1) / ((j + 2).factorial : ℝ) with hg
  have hIcc : Finset.Icc 2 N = Finset.Ico 2 (N + 1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have hre : ∑ k ∈ Finset.Icc 2 N, 2 * (p ^ k)⁻¹ * X ^ (k - 1) / (k.factorial : ℝ) =
      ∑ j ∈ Finset.range (N + 1 - 2), g j := by
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hg]
    simp only
    rw [show 2 + j = j + 2 from Nat.add_comm 2 j, show j + 2 - 1 = j + 1 by omega]
  have hnn : ∀ j, 0 ≤ g j := fun j => by rw [hg]; positivity
  rw [hre]
  calc ∑ j ∈ Finset.range (N + 1 - 2), g j ≤ ∑' j, g j :=
        hsum.sum_le_tsum _ fun j _ => hnn j
    _ ≤ Real.exp (3 / 8) * X / p ^ 2 := htsum
    _ ≤ 1.5 * X / p ^ 2 := hexp
end RestKSumBound
end GroundTheory.Heights₂.Heights.RestTerms
