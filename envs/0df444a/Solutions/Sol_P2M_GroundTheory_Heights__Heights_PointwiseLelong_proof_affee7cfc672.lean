-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointwiseLelong_proof_affee7cfc672
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:48:31.15037+00:00
-- url     : https://prove2.me/submissions/a6b9a687-29b8-4669-aa92-c97aec7291ca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_sphereIntegrable_log_6df905eb445b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_main_bound_fdf9c91e7ac8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_exists_max_c79fae73757f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_eval_ne_zero_of_max_d14cb858f69d

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
open PointwiseLelong
namespace GroundTheory.Heights₂.Heights
namespace PointwiseLelong
theorem _root_.solution (h1 : SphereProjectionLaw.Statement) : PointwiseLelong.Statement := by
  intro N d Q hQ0 hQ
  refine ⟨fun p hp hQp => ⟨sphereIntegrable_log hQ0, main_bound h1 hQ0 hQ p hp hQp⟩, fun hN => ?_⟩
  obtain ⟨p, hp, hmax⟩ := exists_max hN Q
  have hQp := eval_ne_zero_of_max hQ0 hQ hp hmax
  have hsup : (⨆ z : {z : Fin N → ℂ // ∑ j, ‖z j‖ ^ 2 = 1}, ‖eval (z : Fin N → ℂ) Q‖) =
      ‖eval p Q‖ := by
    have : Nonempty {z : Fin N → ℂ // ∑ j, ‖z j‖ ^ 2 = 1} := ⟨⟨p, hp⟩⟩
    exact le_antisymm (ciSup_le fun z => hmax z z.2)
      (le_ciSup_of_le ⟨‖eval p Q‖, by rintro _ ⟨z, rfl⟩; exact hmax z z.2⟩ ⟨p, hp⟩ le_rfl)
  rw [hsup]
  exact main_bound h1 hQ0 hQ p hp hQp
end PointwiseLelong
end GroundTheory.Heights₂.Heights
