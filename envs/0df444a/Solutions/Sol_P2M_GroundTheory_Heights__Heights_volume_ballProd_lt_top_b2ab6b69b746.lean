-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_volume_ballProd_lt_top_b2ab6b69b746
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:41:24.200182+00:00
-- url     : https://prove2.me/submissions/597daa4b-ba14-45c4-966f-df1eaa7809ba

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isBounded_ballProd_f634cf668f3e

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
open MvPolynomial MeasureTheory NumberField
noncomputable section
open Matrix
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (h : HermNorm n) (k : ℕ) : volume (ballProd h k) < ⊤ :=
  (isBounded_ballProd h k).measure_lt_top
end GroundTheory.Heights₂.Heights
