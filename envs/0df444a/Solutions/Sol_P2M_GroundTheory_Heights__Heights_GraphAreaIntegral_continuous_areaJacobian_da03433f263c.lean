-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GraphAreaIntegral_continuous_areaJacobian_da03433f263c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:06.348314+00:00
-- url     : https://prove2.me/submissions/fd04f4b6-5875-4b08-a3b1-6380267f3717

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGraphAreaIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGraphAreaFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PGraphAreaIntegral

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
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace GraphAreaIntegral
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] :
    Continuous fun M : E →L[ℝ] F => areaJacobian (M : E →ₗ[ℝ] F) := by
  have h : (fun M : E →L[ℝ] F => areaJacobian (M : E →ₗ[ℝ] F)) =
      fun M => √((ContinuousLinearMap.adjoint M ∘L M).det) := by
    funext M
    rfl
  rw [h]
  exact (ContinuousLinearMap.continuous_det.comp
    ((ContinuousLinearMap.adjoint.continuous).clm_comp continuous_id)).sqrt
end GraphAreaIntegral
end GroundTheory.Heights₂.Heights
