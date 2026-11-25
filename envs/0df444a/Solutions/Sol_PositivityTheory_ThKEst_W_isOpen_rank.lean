-- Prove2me | solution 1 for PositivityTheory.ThKEst.W.isOpen_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:21.976186+00:00
-- url     : https://prove2.me/submissions/1414af22-b17b-41b5-8de8-cb1866e47fba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_RankIffRight
import Theorems.Thm_PositivityTheory_ThKEst_W_rank_iff_det

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
theorem _root_.solution [TopologicalSpace k] [IsTopologicalRing k] [T1Space k] :
    IsOpen {Y : Matrix (Fin n) (Fin d) k | Y.rank = n} := by
  have hset : {Y : Matrix (Fin n) (Fin d) k | Y.rank = n} =
      ⋃ C : Matrix (Fin d) (Fin n) k, {Y | (Y * C).det ≠ 0} := by
    ext Y
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, rank_iff_det]
  rw [hset]
  refine isOpen_iUnion fun C => ?_
  exact isOpen_compl_singleton.preimage (Continuous.matrix_det (continuous_id.matrix_mul continuous_const))
end PositivityTheory.ThKEst.W
