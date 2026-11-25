-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutLieLast_proof_29cd00a067fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:19:32.582628+00:00
-- url     : https://prove2.me/submissions/08147cba-286a-4102-98ec-d58a04ae27cf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutLieLast
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutLieLast_transport_smallPowerSum_8cdf674c2e5b

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace RestCutLieLast
theorem _root_.solution : RestCutLieLast.Statement := by
  intro f j k _ m σ
  obtain ⟨τ, b⟩ := σ
  cases b with
  | true =>
    refine ⟨(-1) ^ m, 0, neg_one_pow_eq_or ℚ m, ?_⟩
    rw [RestCutLieLast.transport_smallPowerSum]
    simp [lieClass]
  | false =>
    refine ⟨-1, 1, Or.inr rfl, ?_⟩
    rw [RestCutLieLast.transport_smallPowerSum]
    simp only [lieClass, rootPsum, Fintype.sum_sum_type, map_one, one_mul]
    simp
end RestCutLieLast
end GroundTheory.Heights₂.Heights
