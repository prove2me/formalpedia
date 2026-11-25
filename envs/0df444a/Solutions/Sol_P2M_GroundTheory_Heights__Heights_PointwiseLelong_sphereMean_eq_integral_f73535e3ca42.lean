-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointwiseLelong_sphereMean_eq_integral_f73535e3ca42
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:49:00.849891+00:00
-- url     : https://prove2.me/submissions/907d88bc-1ded-4d7c-a6bd-cd25eb5166d8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_normalize_373300d892cc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sphereMean_eq_8b9830c2c5f6


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
theorem _root_.solution {f : (Fin N → ℂ) → ℝ} (hf : Measurable f) :
    sphereMean (HermNorm.std N) 1 (fun u => f (fun j => u (0, j))) = ∫ z, f z ∂sphereLaw N := by
  rw [sphereLaw, integral_map measurable_normalize.aemeasurable hf.aestronglyMeasurable,
    sphereMean_eq, average, Measure.restrict_apply_univ]
  rfl
end GroundTheory.Heights₂.Heights.PointwiseLelong
