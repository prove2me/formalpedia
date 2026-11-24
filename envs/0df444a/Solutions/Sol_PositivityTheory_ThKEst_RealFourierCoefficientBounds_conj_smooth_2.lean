-- Prove2me | solution 2 for PositivityTheory.ThKEst.RealFourierCoefficientBounds.conj_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:57.089223+00:00
-- url     : https://prove2.me/submissions/e7a21ec3-dd94-40dd-8052-083de8bd116b

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_CoefRealA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.RealFourierCoefficientBounds
open MeasureTheory SchwartzMap
open scoped FourierTransform ContDiff
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
namespace PositivityTheory.ThKEst.RealFourierCoefficientBounds
theorem _root_.solution (f : SchwartzMap V ℂ) : ContDiff ℝ ∞ fun u => (starRingEnd ℂ) (f u) :=
  Complex.conjCLE.contDiff.comp (f.smooth ⊤)
end PositivityTheory.ThKEst.RealFourierCoefficientBounds
