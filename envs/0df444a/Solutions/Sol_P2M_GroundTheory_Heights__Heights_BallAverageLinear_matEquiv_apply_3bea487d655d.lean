-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BallAverageLinear_matEquiv_apply_3bea487d655d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:23.491259+00:00
-- url     : https://prove2.me/submissions/af079812-d4f0-48f1-bb65-fe746af6c79f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PBallAverageLinear

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
open MeasureTheory Measure Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.BallAverageLinear
namespace GroundTheory.Heights₂.Heights.BallAverageLinear
theorem _root_.solution {n : ℕ} (h : HermNorm n) (v : Fin n → ℂ) : matEquiv h v = h.mat *ᵥ v := rfl
end GroundTheory.Heights₂.Heights.BallAverageLinear
