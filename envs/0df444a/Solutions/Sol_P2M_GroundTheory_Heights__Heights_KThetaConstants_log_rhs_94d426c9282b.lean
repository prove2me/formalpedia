-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KThetaConstants_log_rhs_94d426c9282b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:01:32.833431+00:00
-- url     : https://prove2.me/submissions/541434da-b96f-45d4-9152-10cf90db33ff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaConstants

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
open Real
open GroundTheory.Heights₂.Heights.KThetaConstants
namespace GroundTheory.Heights₂.Heights.KThetaConstants
theorem _root_.solution (C ρ d : ℝ) (g : ℕ) (hd : 0 < d) :
    Real.log (((2 : ℝ) ^ g * d) ^ (-(1 / 4 : ℝ)) *
        exp (g * Real.log (1 + 1 / ρ) + C * g * Real.log (2 * g))) =
      (-(1 / 4)) * (g * Real.log 2 + Real.log d) +
        (g * Real.log (1 + 1 / ρ) + C * g * Real.log (2 * g)) := by
  have h1 : 0 < (2 : ℝ) ^ g * d := by positivity
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow h1, Real.log_exp,
    Real.log_mul (by positivity) hd.ne', Real.log_pow]
end GroundTheory.Heights₂.Heights.KThetaConstants
