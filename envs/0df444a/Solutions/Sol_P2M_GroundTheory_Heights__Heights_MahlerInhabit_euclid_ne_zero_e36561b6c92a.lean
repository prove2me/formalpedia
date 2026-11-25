-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MahlerInhabit_euclid_ne_zero_e36561b6c92a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:06:49.311406+00:00
-- url     : https://prove2.me/submissions/0f2e7e49-efbb-480d-b3f1-6235456f37c0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler

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
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}
open GroundTheory.Heights₂.Heights.MahlerInhabit
namespace GroundTheory.Heights₂.Heights.MahlerInhabit
theorem _root_.solution : (EuclideanSpace.single 0 1 : EuclideanSpace ℂ (Fin 1)) ≠ 0 := by
  intro h0
  have := congrArg (fun y : EuclideanSpace ℂ (Fin 1) => y 0) h0
  simp at this
end GroundTheory.Heights₂.Heights.MahlerInhabit
