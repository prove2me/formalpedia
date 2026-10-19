-- Prove2me | solution 1 for SchwartzMap.PoissonSummation.Standard.fourier_character_projection_exponential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/2aa8d649-58dc-47d7-b2c9-90d0c502912d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_fourier_character_euclidean_projection

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
    UnitAddTorus.mFourier n (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) =
      Complex.exp
        (2 * Real.pi * Complex.I *
          ⟪x, SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n⟫_[ℝ]) := by
  have hinner :
      inner ℝ x (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n) =
        RCLike.wInner (𝕜 := ℝ) 1 x.ofLp
          (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n).ofLp :=
    RCLike.inner_eq_wInner_one x (embeddedIntegerVector n)
  simpa [Real.fourierChar_apply, mul_assoc, mul_comm, hinner] using!
    (fourier_character_euclidean_projection (d := d) (n := n) (x := x))
end SchwartzMap.PoissonSummation.Standard
