-- Prove2me | solution 1 for P2M_PositivityTheory_ThKR_Mp_C_toBlocks___mul_lo_68e53e420ba7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:32:27.221035+00:00
-- url     : https://prove2.me/submissions/26cffd3c-287d-40bc-96d0-4a9a98dd8864

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
theorem _root_.solution (s : Mat l) (t : ℝ) : (s * lo t).toBlocks₁₁ = s.toBlocks₁₁ + t • s.toBlocks₁₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks s, lo, fromBlocks_multiply, toBlocks_fromBlocks₁₁]
  simp
end PositivityTheory.ThKR.Mp.C
