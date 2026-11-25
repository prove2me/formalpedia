-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutLieFirst_proof_fef809d9072b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:32:14.877796+00:00
-- url     : https://prove2.me/submissions/d161869f-610b-4836-9cbb-ff24aaab9487

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutLieFirst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutLieFirst_transport_smallPowerSum_9e1dd0b87844

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
namespace RestCutLieFirst
theorem _root_.solution : RestCutLieFirst.Statement := by
  intro f j k _ m σ
  obtain ⟨τ, b⟩ := σ
  have hC1 : (C ((((-1 : ℚ) ^ m : ℚ) : ℝ)) : RootPoly f j k) = (-1) ^ m := by simp
  have hC2 : (C (((-1 : ℚ) : ℚ) : ℝ) : RootPoly f j k) = -1 := by simp
  have hC3 : (C ((-1 : ℝ) ^ m) : RootPoly f j k) = (-1) ^ m := by simp
  cases b with
  | false =>
    refine ⟨(-1) ^ m, 0, neg_one_pow_eq_or ℚ m, ?_⟩
    rw [RestCutLieFirst.transport_smallPowerSum, hC1]
    simp only [lieClass, map_zero, zero_mul, add_zero]
    rw [← mul_assoc, ← mul_pow]
    simp
  | true =>
    refine ⟨-1, (-1) ^ m, Or.inr rfl, ?_⟩
    rw [RestCutLieFirst.transport_smallPowerSum, hC2, hC3]
    simp only [lieClass, rootPsum, Fintype.sum_sum_type]
    ring
end RestCutLieFirst
end GroundTheory.Heights₂.Heights
