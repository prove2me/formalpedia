-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KThetaCharIntegral_torusChar_eq_prod_1de5f9bae33f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:01:30.386803+00:00
-- url     : https://prove2.me/submissions/e98e38cf-58fe-47e5-8ee5-dd2500f450b8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaCharIntegral

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
open Real MeasureTheory
noncomputable section
open GroundTheory.Heights₂.Heights.KThetaCharIntegral
namespace GroundTheory.Heights₂.Heights.KThetaCharIntegral
theorem _root_.solution {g : ℕ} (m : Fin g → ℤ) (u : Fin g → ℝ) :
    torusChar m u = ∏ i, Complex.exp (2 * π * Complex.I * ((m i : ℂ) * (u i : ℂ))) := by
  unfold torusChar
  rw [Finset.mul_sum, Complex.exp_sum]
end GroundTheory.Heights₂.Heights.KThetaCharIntegral
