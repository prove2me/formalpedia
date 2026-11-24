-- Prove2me | solution 1 for PositivityTheory.ThKEst.W.rank_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:32:38.950547+00:00
-- url     : https://prove2.me/submissions/6b0e3ca2-766d-4ec2-9b3c-6e6f95919995

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_RankIffRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology GlobalTheory.WeilM
open scoped Pointwise
noncomputable section
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.W
variable {k : Type} [Field k] {n d : ℕ}
namespace PositivityTheory.ThKEst.W
theorem _root_.solution (A : Matrix (Fin n) (Fin n) k) (Y : Matrix (Fin n) (Fin d) k) (B : Matrix (Fin d) (Fin d) k)
    (h : (A * Y * B).rank = n) : Y.rank = n := by
  apply le_antisymm (Matrix.rank_le_height Y)
  calc n = (A * Y * B).rank := h.symm
    _ ≤ (A * Y).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Y.rank := Matrix.rank_mul_le_right _ _
end PositivityTheory.ThKEst.W
