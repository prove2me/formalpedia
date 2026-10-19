-- Prove2me | solution 1 for SchwartzMap.PoissonSummation.Standard.fourier_character_euclidean_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/7a60e05d-3f8c-4aa6-ba36-8254bb5337e4

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SchwartzMap_PoissonSummation_Standard_negative_fourier_character_projection

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
      (𝐞 (inner ℝ x (SchwartzMap.PoissonSummation.Standard.embeddedIntegerVector (d := d) n)) : ℂ) := by
  simpa [embedded_integer_vector_neg (d := d) (n := n), inner_neg_right, neg_neg] using!
    (negative_fourier_character_projection (d := d) (n := -n) (x := x))
end SchwartzMap.PoissonSummation.Standard
