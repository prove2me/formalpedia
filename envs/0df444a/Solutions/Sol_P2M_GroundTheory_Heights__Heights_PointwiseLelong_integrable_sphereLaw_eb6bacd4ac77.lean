-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointwiseLelong_integrable_sphereLaw_eb6bacd4ac77
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:03:02.65046+00:00
-- url     : https://prove2.me/submissions/9af57866-992e-45ef-aeb8-5d174e942874

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_normalize_373300d892cc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_volume_sphereBall_ne_zero_20c0131a104a

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
theorem _root_.solution {f : (Fin N → ℂ) → ℝ} (hf : Measurable f)
    (hi : SphereIntegrable (HermNorm.std N) 1 (fun u => f (fun j => u (0, j)))) :
    Integrable f (sphereLaw N) := by
  rw [sphereLaw, integrable_map_measure hf.aestronglyMeasurable measurable_normalize.aemeasurable]
  exact hi.smul_measure (ENNReal.inv_ne_top.mpr volume_sphereBall_ne_zero)
end GroundTheory.Heights₂.Heights.PointwiseLelong
