-- Prove2me | solution 1 for PositivityTheory.ThKEst.RealFourierCoefficientBounds.H_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:06.398809+00:00
-- url     : https://prove2.me/submissions/4e7467fa-4792-4be4-b41c-cf07ff6c8589

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_CoefRealA
import Theorems.Thm_PositivityTheory_ThKEst_RealFourierCoefficientBounds_conj_smooth
import Theorems.Thm_PositivityTheory_ThKEst_RealFourierCoefficientBounds_shift_smooth

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
theorem _root_.solution (f₁ f₂ : SchwartzMap V ℂ) (x : V) : ContDiff ℝ ∞ (H f₁ f₂ x) :=
  (shift_smooth f₁ x).mul (conj_smooth f₂)
end PositivityTheory.ThKEst.RealFourierCoefficientBounds
