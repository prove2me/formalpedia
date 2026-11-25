-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_shifted_apply_of_apply_eq_zero_c2e11a789312
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:04:59.003738+00:00
-- url     : https://prove2.me/submissions/c65ba89b-0781-4ba1-8fc8-2fe018828ba9

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
theorem _root_.solution (A : E →L[ℂ] F) (ε : ℝ) {z : E} (hz : A z = 0) :
    shifted A ε z = (ε : ℂ) • z := by
  simp [shifted, hz]
end GroundTheory.Heights₂.Heights.KernelProjMeasurable
