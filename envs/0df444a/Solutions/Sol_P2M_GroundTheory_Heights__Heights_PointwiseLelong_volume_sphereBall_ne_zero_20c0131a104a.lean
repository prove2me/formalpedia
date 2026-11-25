-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointwiseLelong_volume_sphereBall_ne_zero_20c0131a104a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:56:26.579033+00:00
-- url     : https://prove2.me/submissions/ce847738-0896-434f-917f-384534be4f5c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_volume_ballProd_pos_bf80568889a6


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
open MvPolynomial MeasureTheory ProbabilityTheory Real
noncomputable section
open GroundTheory.Heights₂.Heights.PointwiseLelong
variable {N : ℕ}
namespace GroundTheory.Heights₂.Heights.PointwiseLelong
theorem _root_.solution : volume (sphereBall (HermNorm.std N) 1) ≠ 0 :=
  (volume_ballProd_pos (HermNorm.std N) 1).ne'
end GroundTheory.Heights₂.Heights.PointwiseLelong
