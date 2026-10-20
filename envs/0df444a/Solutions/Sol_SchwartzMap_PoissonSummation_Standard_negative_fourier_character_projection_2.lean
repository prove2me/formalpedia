-- Prove2me | solution 2 for SchwartzMap.PoissonSummation.Standard.negative_fourier_character_projection
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:32:25.819671+00:00
-- url     : https://prove2.me/submissions/2863b738-e674-44cf-aced-34d110728db4

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
    UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) =
      (𝐞 (-(inner ℝ x (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n))) : ℂ) := by
  have hin : inner ℝ x (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n) =
      ∑ i, x i * (n i : ℝ) := by
    simp [PiLp.inner_apply, mul_comm]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    PoissonSummation.Standard.euclideanTorusProjection, UnitAddTorus.coordinateTorusProjection,
    Pi.neg_apply]
  simp_rw [fourier_coe_apply]
  rw [Real.fourierChar_apply, ← Complex.exp_sum, hin]
  congr 1
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib, mul_neg, neg_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

