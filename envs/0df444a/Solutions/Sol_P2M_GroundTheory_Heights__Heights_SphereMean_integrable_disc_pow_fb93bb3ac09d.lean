-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_integrable_disc_pow_fb93bb3ac09d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:18:13.071237+00:00
-- url     : https://prove2.me/submissions/630283da-8440-4dc5-86cb-259d55cf86eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanCalc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanDisc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_integrable_disc_radial_b2316b4572c9

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
open MeasureTheory Measure Set Real
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean
namespace GroundTheory.Heights₂.Heights.SphereMean
theorem _root_.solution (m : ℕ) :
    Integrable (fun z : ℂ => (Iio (1 : ℝ)).indicator (fun r => (1 - r ^ 2) ^ m) ‖z‖) :=
  integrable_disc_radial _ (by fun_prop)
end GroundTheory.Heights₂.Heights.SphereMean
