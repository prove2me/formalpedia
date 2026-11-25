-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.C.lo_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:32:34.299136+00:00
-- url     : https://prove2.me/submissions/7fc9d2bb-a1df-4ad2-9396-0664ee40b07d

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MapOfRealMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL
open scoped Real
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open C
open PositivityTheory.ThKR.Mp.C
namespace PositivityTheory.ThKR.Mp.C
theorem _root_.solution (t : ℝ) : lo (l := l) t ∈ Matrix.symplecticGroup l ℝ := by
  rw [SymplecticGroup.mem_iff, lo, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp
end PositivityTheory.ThKR.Mp.C
