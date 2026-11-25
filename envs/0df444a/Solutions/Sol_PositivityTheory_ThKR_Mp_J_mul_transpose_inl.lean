-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.J_mul_transpose_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:32:59.062397+00:00
-- url     : https://prove2.me/submissions/fd1deb89-c9e9-4235-bfb7-969a00005151

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
theorem _root_.solution (s : Mat l) (a : l) (j : l ⊕ l) :
    (Matrix.J l ℝ * sᵀ) (.inl a) j = -s j (.inr a) := by
  simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
end PositivityTheory.ThKR.Mp
