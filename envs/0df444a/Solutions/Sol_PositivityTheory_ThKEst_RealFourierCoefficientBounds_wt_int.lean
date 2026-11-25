-- Prove2me | solution 1 for PositivityTheory.ThKEst.RealFourierCoefficientBounds.wt_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:24.298835+00:00
-- url     : https://prove2.me/submissions/32f0bf97-d434-4597-81d8-3e049e75f2a5

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
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
namespace PositivityTheory.ThKEst.RealFourierCoefficientBounds
theorem _root_.solution : Integrable fun u : V => ((1 + ‖u‖) ^ (Module.finrank ℝ V + 1))⁻¹ := by
  have h := integrable_one_add_norm (E := V) (μ := volume) (r := ((Module.finrank ℝ V + 1 : ℕ) : ℝ))
    (by push_cast; linarith)
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
end PositivityTheory.ThKEst.RealFourierCoefficientBounds
