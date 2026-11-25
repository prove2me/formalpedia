-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_integral_ballSet_neg_log_sqNorm_e9c057af6227
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:36:48.851579+00:00
-- url     : https://prove2.me/submissions/11f79d06-62c2-4bab-aba8-bf708d387791

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_lintegral_ballSet_neg_log_sqNorm_45f854ab08a5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_integrableOn_and_integral_of_lintegral_99de7075dac1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_measurableSet_ballSet_d8b80531e855
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_measurable_sqNorm_950a20036208
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_nonneg_b8444e370306
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_volume_ballSet_one_ne_top_34fed7d837d3


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
    IntegrableOn (fun x : Fin (m + 1) → ℂ => -log (sqNorm x)) (ballSet (m + 1) 1) ∧
      ∫ x in ballSet (m + 1) 1, -log (sqNorm x) = 1 / (m + 1) * volume.real (ballSet (m + 1) 1) :=
  integrableOn_and_integral_of_lintegral (measurableSet_ballSet _ _)
    (volume_ballSet_one_ne_top _) (f := fun x : Fin (m + 1) → ℂ => -log (sqNorm x))
    ((measurable_sqNorm _).log.neg)
    (fun x hx => by
      rw [neg_nonneg]
      exact log_nonpos (sqNorm_nonneg x) (le_of_lt hx))
    (by positivity) (lintegral_ballSet_neg_log_sqNorm m)
end GroundTheory.Heights₂.Heights.SphereMean
