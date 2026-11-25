-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointwiseLelong_sphereIntegrable_coord_e75478f7b92c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:56:15.557027+00:00
-- url     : https://prove2.me/submissions/3307668d-27cf-4b7f-a050-cf0a9e60906d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_mahler_2b6fa8e526b5


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
theorem _root_.solution {p : Fin N → ℂ} (hp : ∑ j, ‖p j‖ ^ 2 = 1) :
    SphereIntegrable (HermNorm.std N) 1 (fun u ↦ Real.log ‖coordAlong p (fun j ↦ u (0, j))‖) := by
  have h : (∑ j, X ((0 : Fin 1), j) * C (star (p j)) : MvPolynomial (Fin 1 × Fin N) ℂ) ≠ 0 := by
    intro h0
    have := congrArg (eval fun ij : Fin 1 × Fin N => p ij.2) h0
    simp only [map_sum, map_mul, eval_X, eval_C, map_zero] at this
    have hj : ∀ j, p j * star (p j) = ((‖p j‖ ^ 2 : ℝ) : ℂ) := fun j => by
      rw [Complex.star_def, Complex.mul_conj']
      push_cast
      ring
    simp_rw [hj] at this
    rw [← Complex.ofReal_sum, hp] at this
    simp at this
  have := (LogInt.integrableOn_log_mahler (HermNorm.std N) _ h).1
  simp only [map_sum, map_mul, eval_X, eval_C] at this
  exact this
end GroundTheory.Heights₂.Heights.PointwiseLelong
