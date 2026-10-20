-- Prove2me | solution 2 for SchwartzMap.PoissonSummation.Standard.fourier_character_projection_exponential
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:48:50.56899+00:00
-- url     : https://prove2.me/submissions/40eec15d-bc4f-4573-bc66-709f27cdd4a6

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped BigOperators FourierTransform
open MeasureTheory
open SchwartzMap SchwartzMap.PoissonSummation SchwartzMap.PoissonSummation.Standard
variable {d : ℕ}
open UnitAddTorus
variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))


theorem solution (n : Fin d → ℤ) (x : (EuclideanSpace ℝ (Fin d))) :
    UnitAddTorus.mFourier n (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) =
      Complex.exp
        (2 * Real.pi * Complex.I *
          ⟪x, SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n⟫_[ℝ]) := by
  change (∏ i : Fin d, fourier (n i) (((WithLp.ofLp x) i : ℝ) : UnitAddCircle)) = _
  simp_rw [fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  have hin : ⟪x, SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n⟫_[ℝ] =
      ∑ i : Fin d, (n i : ℝ) * x i := by
    rw [RCLike.wInner_one_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [real_inner_eq_re_inner, mul_comm]
  rw [hin]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

