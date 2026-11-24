-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CoinvStaircaseDegree_proof_96f3a35ebb69
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:52:10.903989+00:00
-- url     : https://prove2.me/submissions/891669de-d992-438d-9bf7-63527ab2b439

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvStaircaseDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_sum_staircase_exponents_9893f3414274

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
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace CoinvStaircaseDegree
theorem _root_.solution : CoinvStaircaseDegree.Statement := by
  intro f n e he
  have hle : ∀ v ∈ (Finset.univ : Finset (Fin f × Fin n)), e v ≤ (v.2 : ℕ) := fun v _ => he v
  rw [Finsupp.degree_eq_sum, ← Coinv.sum_staircase_exponents f n]
  refine ⟨Finset.sum_le_sum hle, fun hEq => ?_⟩
  have hall := (Finset.sum_eq_sum_iff_of_le hle).1 hEq
  ext v
  simp [staircase, hall v (Finset.mem_univ v)]
end CoinvStaircaseDegree
end GroundTheory.Heights₂.Heights.RestTerms
