-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.metaplectic_unipotent_block_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:46:09.539291+00:00
-- url     : https://prove2.me/submissions/0ddd0d83-8709-401f-b001-e45df180fb8c

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MetaplecticUnipotentBlockSecondDiag
import Theorems.Thm_PositivityTheory_ThKR_Mp_tc_apply
import Theorems.Thm_PositivityTheory_ThKR_LL_bl_apply


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
theorem _root_.solution (S : Matrix l l ℝ) (t : ℝ) :
    bl Sum.inl Sum.inr (nn S t) = t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S := by
  ext x a
  simp [bl_apply, nn, tc_apply, Finset.mul_sum, mul_assoc]
end PositivityTheory.ThKR.Mp
