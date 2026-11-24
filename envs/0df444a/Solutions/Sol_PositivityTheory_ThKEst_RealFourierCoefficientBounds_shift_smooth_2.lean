-- Prove2me | solution 2 for PositivityTheory.ThKEst.RealFourierCoefficientBounds.shift_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:57.266363+00:00
-- url     : https://prove2.me/submissions/cda7f7e8-5990-45ed-b21b-6a8372a6513c

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
theorem _root_.solution (f : SchwartzMap V ℂ) (x : V) : ContDiff ℝ ∞ fun u => f (u + x) :=
  (f.smooth ⊤).comp (contDiff_id.add contDiff_const)
end PositivityTheory.ThKEst.RealFourierCoefficientBounds
