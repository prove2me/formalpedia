-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.qPart_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:49.859933+00:00
-- url     : https://prove2.me/submissions/cd29b620-979a-46f1-88d5-f2fdeb5d7fe4

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_NormExpSubLe
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalLift
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
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l] [DecidableEq l]
namespace PositivityTheory.ThKR.LL
theorem _root_.solution (g : Matrix (l ⊕ l) (l ⊕ l) ℝ) (w : l ⊕ l → ℝ) :
    qPart (g *ᵥ w) = bl Sum.inr Sum.inl g (pPart w) + bl Sum.inr Sum.inr g (qPart w) := by
  ext a
  simp [bl_apply, pPart, qPart, mulVec, dotProduct]
end PositivityTheory.ThKR.LL
