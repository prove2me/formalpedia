-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.nn_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:31:27.805247+00:00
-- url     : https://prove2.me/submissions/78cbfb92-9da0-4b7d-bcd2-849fa8f42822

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MetaplecticUnipotentBlockSecondDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
namespace PositivityTheory.ThKR.Mp
theorem _root_.solution {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) : nn S t ∈ Matrix.symplecticGroup l ℝ := by
  rw [SymplecticGroup.mem_iff, nn, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp [hS.eq]
end PositivityTheory.ThKR.Mp
