-- Prove2me | solution 1 for PositivityTheory.ThKEst.LinDerPf.Gr.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:11.690473+00:00
-- url     : https://prove2.me/submissions/9d32f70c-392e-4d9f-a6bf-2807ae2ab7c6

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_LinDerA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.LinDerPf
open Filter Topology Asymptotics
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
variable {a : A →L[ℝ] A}
namespace PositivityTheory.ThKEst.LinDerPf
namespace Gr
theorem _root_.solution (ha : ∀ x y, a (x * y) = a y * a x) {g h : A} (hg : Gr a g) (hh : Gr a h) : Gr a (g * h) := by
  constructor
  · rw [ha, mul_assoc, ← mul_assoc (a g), hg.1, one_mul, hh.1]
  · rw [ha, mul_assoc, ← mul_assoc h, hh.2, one_mul, hg.2]
end Gr
end PositivityTheory.ThKEst.LinDerPf
