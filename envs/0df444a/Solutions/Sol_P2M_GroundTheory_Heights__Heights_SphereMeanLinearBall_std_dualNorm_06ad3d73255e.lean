-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMeanLinearBall_std_dualNorm_06ad3d73255e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:54.601904+00:00
-- url     : https://prove2.me/submissions/a66fa2c5-accc-42e8-988e-ae497c6e4cb6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSphereMeanLinearBall

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
open MeasureTheory Set
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMeanLinearBall
namespace GroundTheory.Heights₂.Heights.SphereMeanLinearBall
theorem _root_.solution (n : ℕ) (y : Fin n → ℂ) :
    (HermNorm.std n).dualNorm y = √(∑ j, ‖y j‖ ^ 2) := by
  simp [HermNorm.dualNorm, HermNorm.std]
end GroundTheory.Heights₂.Heights.SphereMeanLinearBall
