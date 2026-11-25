-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBound_ReductionSmallLast_proof_9930e9497297
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:08:01.580261+00:00
-- url     : https://prove2.me/submissions/af8795a6-8b18-423f-96a6-7f0af295ab5b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_PReductionSmallLast
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBound_ReductionSmallLast_b0_le_small_block_last_3c1e76273940

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBound
open Real
namespace GroundTheory.Heights₂.Heights.LowerBound
namespace ReductionSmallLast
theorem _root_.solution : ReductionSmallLast.Statement := by
  intro K1 Ca Cc hK1 hCa hCc
  refine ⟨2 * (K1 + (1 / 2 + Ca + Cc)), ?_⟩
  intro A0 b0 hh sl rest vol J f j' n N j La h
  have hb0 := ReductionSmallLast.b0_le_small_block_last h
  have hN : 0 < N := lt_of_lt_of_le one_pos h.one_le_N
  have hLa : 0 < La := lt_of_lt_of_le one_pos h.one_le_La
  have hsum : -(K1 * N * La) ≤ j * A0 + N * b0 := (abs_le.mp h.bound_sum).1
  have hNb0 : N * b0 ≤ N * ((1 / 2 + Ca + Cc) * La) := mul_le_mul_of_nonneg_left hb0 hN.le
  set K := K1 + (1 / 2 + Ca + Cc) with hKdef
  have hK : 0 ≤ K := by positivity

  have hexp : N * (K * La) = K1 * N * La + N * ((1 / 2 + Ca + Cc) * La) := by
    rw [hKdef]; ring
  have hjA : -(N * (K * La)) ≤ j * A0 := by linarith

  have hNj : N * (K * La) ≤ j * (2 * K * La) := by
    have hKLa : 0 ≤ K * La := mul_nonneg hK hLa.le
    nlinarith [h.half_N_le_j]
  have : j * (-(2 * K * La)) ≤ j * A0 := by linarith
  have := le_of_mul_le_mul_left this h.j_pos
  linarith
end ReductionSmallLast
end GroundTheory.Heights₂.Heights.LowerBound
