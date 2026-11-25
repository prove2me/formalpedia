-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_tendsto_resolvent_de8987e0176b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:19:59.300034+00:00
-- url     : https://prove2.me/submissions/389a8d94-4685-4c27-87ea-dab233e368ad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsKernelProjMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PKernelProjMeasurable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KernelProjMeasurable_exists_norm_resolvent_sub_le_a3ab1eb835f6

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
theorem _root_.solution (A : E →L[ℂ] F) :
    Tendsto (fun j : ℕ => resolvent A (1 / ((j : ℝ) + 1))) atTop
      (𝓝 (LinearMap.ker (A : E →ₗ[ℂ] F)).starProjection) := by
  obtain ⟨C, hC⟩ := exists_norm_resolvent_sub_le A
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun j => hC _ (by positivity)) ?_
  simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
end GroundTheory.Heights₂.Heights.KernelProjMeasurable
