-- Prove2me | solution 1 for SchwartzMap.PoissonSummation.Standard.torus_descended_periodization_comp_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/2e9d936f-7610-42cc-ac67-5cc8448a4dd5

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
namespace SchwartzMap.PoissonSummation.Standard
theorem _root_.solution (x : (EuclideanSpace ℝ (Fin d))) :
    torusDescendedPeriodization (d := d) f (PoissonSummation.Standard.euclideanTorusProjection (d := d) x) =
      latticePeriodizedMap (d := d) f x := by
  have hcomp : (torusDescendedPeriodization (d := d) f).comp (euclideanTorusProjectionContinuous (d := d)) = latticePeriodizedMap (d := d) f := by
    simp [torusDescendedPeriodization]
  simpa [euclideanTorusProjectionContinuous] using! congrArg (fun g : C((EuclideanSpace ℝ (Fin d)), ℂ) => g x) hcomp
end SchwartzMap.PoissonSummation.Standard
