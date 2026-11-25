-- Prove2me | solution 1 for PositivityTheory.ThKEst.RealFourierCoefficientBounds.q_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:21.209066+00:00
-- url     : https://prove2.me/submissions/42840266-9f68-420a-b56d-7874202e696d

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
theorem _root_.solution (M N : ℕ) : Continuous (q V M N) := by
  unfold q
  exact Seminorm.continuous_finsetSup (E := SchwartzMap V ℂ) (s := Finset.Iic (M, N))
    fun m _ => (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm m
end PositivityTheory.ThKEst.RealFourierCoefficientBounds
