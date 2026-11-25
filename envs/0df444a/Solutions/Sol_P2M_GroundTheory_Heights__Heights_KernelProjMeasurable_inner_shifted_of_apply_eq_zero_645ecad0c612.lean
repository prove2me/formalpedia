-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_inner_shifted_of_apply_eq_zero_645ecad0c612
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:28:18.08921+00:00
-- url     : https://prove2.me/submissions/4127b889-1fcb-4765-b08d-18cb1fead922

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsKernelProjMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PKernelProjMeasurable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology ContinuousLinearMap
noncomputable section
open GroundTheory.Heights₂.Heights.KernelProjMeasurable
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
namespace GroundTheory.Heights₂.Heights.KernelProjMeasurable
theorem _root_.solution (A : E →L[ℂ] F) (ε : ℝ) (u : E) {z : E} (hz : A z = 0) :
    inner ℂ z (shifted A ε u) = (ε : ℂ) * inner ℂ z u := by
  simp [shifted, inner_add_right, inner_smul_right, adjoint_inner_right, hz]
end GroundTheory.Heights₂.Heights.KernelProjMeasurable
