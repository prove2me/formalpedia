-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TangentGaussMoment_hypotheses_inhabited_4b4a554b996a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:14:28.436029+00:00
-- url     : https://prove2.me/submissions/8854364b-66e8-4e88-8977-90a46ba896a3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage

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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section
variable {m n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace TangentGaussMoment
theorem _root_.solution : 0 < 1 ∧ 1 ≤ 2 := by
  norm_num
end TangentGaussMoment
end GroundTheory.Heights₂.Heights
