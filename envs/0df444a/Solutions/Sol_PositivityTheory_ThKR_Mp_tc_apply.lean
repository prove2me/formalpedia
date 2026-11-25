-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.tc_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:30:44.970108+00:00
-- url     : https://prove2.me/submissions/cad0770e-81ef-46ce-be15-8e4ec2b2c919

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
theorem _root_.solution (M : Matrix l l ℝ) (x : Eu l) (a : l) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) M x a = ∑ b, M a b * x b := rfl
end PositivityTheory.ThKR.Mp
