-- Prove2me | solution 1 for SchwartzMap.PoissonSummation.Standard.negative_fourier_character_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/9fc761d0-8531-4749-96e7-e4846969bb6f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SchwartzMap_UnitAddTorus_fourier_character_coordinate_projection_ofLp

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
namespace SchwartzMap.PoissonSummation.Standard
theorem _root_.solution (n : Fin d → ℤ) (x : (EuclideanSpace ℝ (Fin d))) :
    UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) =
      (𝐞 (-(inner ℝ x (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n))) : ℂ) := by
  simp [PoissonSummation.Standard.euclideanTorusProjection, UnitAddTorus.fourier_character_coordinate_projection_ofLp,
    Real.fourierChar_apply, SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector, PiLp.inner_apply,
    Finset.sum_neg_distrib, mul_assoc, mul_comm]
end SchwartzMap.PoissonSummation.Standard
