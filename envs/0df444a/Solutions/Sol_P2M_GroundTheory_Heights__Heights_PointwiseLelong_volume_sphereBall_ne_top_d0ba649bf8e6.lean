-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointwiseLelong_volume_sphereBall_ne_top_d0ba649bf8e6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:48:48.404661+00:00
-- url     : https://prove2.me/submissions/122e49df-9eb4-4beb-b45c-19c85fe32918

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong
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
open MvPolynomial MeasureTheory ProbabilityTheory Real
noncomputable section
open GroundTheory.Heights₂.Heights.PointwiseLelong
variable {N : ℕ}
namespace GroundTheory.Heights₂.Heights.PointwiseLelong
theorem _root_.solution : volume (sphereBall (HermNorm.std N) 1) ≠ ⊤ :=
  (volume_ballProd_lt_top (HermNorm.std N) 1).ne
end GroundTheory.Heights₂.Heights.PointwiseLelong
