-- Prove2me | solution 1 for PositivityTheory.ThKEst.W.rank_iff_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:33.357938+00:00
-- url     : https://prove2.me/submissions/a5b265bd-1b3c-4c92-a974-32e5c36ef2cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_RankIffRight
import Theorems.Thm_PositivityTheory_ThKEst_W_rank_iff_right

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
theorem _root_.solution (Y : Matrix (Fin n) (Fin d) k) : Y.rank = n ↔ ∃ C : Matrix (Fin d) (Fin n) k, (Y * C).det ≠ 0 := by
  rw [rank_iff_right]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, by rw [hC, det_one]; exact one_ne_zero⟩
  · rintro ⟨C, hC⟩
    refine ⟨C * (Y * C)⁻¹, ?_⟩
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hC)]
end PositivityTheory.ThKEst.W
