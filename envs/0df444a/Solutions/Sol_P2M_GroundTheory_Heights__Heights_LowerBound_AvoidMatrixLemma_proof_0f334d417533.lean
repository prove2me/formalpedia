-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBound_AvoidMatrixLemma_proof_0f334d417533
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:49:24.111828+00:00
-- url     : https://prove2.me/submissions/1eb55868-0066-4842-a704-fca47824c3c8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_PAvoidMatrixLemma

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
namespace AvoidMatrixLemma
theorem _root_.solution : AvoidMatrixLemma.Statement := by
  intro a c N x ha hc hN hx
  have hs : 0 < c + 2 * a * N := by positivity
  have ht : 0 < c + N * x := by positivity

  have hlog : log (c + N * x) - log (c + 2 * a * N)
      ≤ (N * (x - 2 * a)) / (c + 2 * a * N) := by
    rw [← Real.log_div ht.ne' hs.ne']
    have h1 := Real.log_le_sub_one_of_pos (div_pos ht hs)
    have h2 : (c + N * x) / (c + 2 * a * N) - 1 = (N * (x - 2 * a)) / (c + 2 * a * N) := by
      field_simp
      ring
    linarith

  have hbound : a * ((N * (x - 2 * a)) / (c + 2 * a * N)) ≤ x / 2 := by
    rcases le_or_gt x (2 * a) with hxa | hxa
    · have : N * (x - 2 * a) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN.le (by linarith)
      have : (N * (x - 2 * a)) / (c + 2 * a * N) ≤ 0 := div_nonpos_of_nonpos_of_nonneg this hs.le
      nlinarith
    · rw [← mul_div_assoc, div_le_iff₀ hs]
      have hpos : 0 < x - 2 * a := by linarith
      nlinarith [mul_pos hc hpos, mul_pos (mul_pos ha hN) hpos]
  have := mul_le_mul_of_nonneg_left hlog ha.le
  nlinarith
end AvoidMatrixLemma
end GroundTheory.Heights₂.Heights.LowerBound
