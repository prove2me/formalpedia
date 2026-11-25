-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_sphereMean_const_6bf8a279dfbc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:56:39.810399+00:00
-- url     : https://prove2.me/submissions/deb3bb71-a5c2-4436-b0f3-78e9bcabd957

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_volume_ballProd_pos_bf80568889a6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_volume_ballProd_lt_top_b2ab6b69b746

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
theorem _root_.solution (h : HermNorm n) (k : ℕ) (a : ℝ) : sphereMean h k (fun _ => a) = a :=
  setAverage_const (volume_ballProd_pos h k).ne' (volume_ballProd_lt_top h k).ne a
end GroundTheory.Heights₂.Heights
