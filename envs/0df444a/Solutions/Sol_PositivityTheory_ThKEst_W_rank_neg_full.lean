-- Prove2me | solution 1 for PositivityTheory.ThKEst.W.rank_neg_full
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:37.031584+00:00
-- url     : https://prove2.me/submissions/17b605a1-fd8a-4077-95ce-8d07a83fcede

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_RankIffRight
import Theorems.Thm_PositivityTheory_ThKEst_W_rank_of_mul

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
theorem _root_.solution {Y : Matrix (Fin n) (Fin d) k} (h : (-Y).rank = n) : Y.rank = n := by
  apply rank_of_mul (-1) Y 1
  simpa using h
end PositivityTheory.ThKEst.W
