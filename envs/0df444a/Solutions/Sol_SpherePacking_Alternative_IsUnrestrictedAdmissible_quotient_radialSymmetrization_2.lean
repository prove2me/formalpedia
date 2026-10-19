-- Prove2me | solution 2 for SpherePacking.Alternative.IsUnrestrictedAdmissible.quotient_radialSymmetrization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:02:03.868527+00:00
-- url     : https://prove2.me/submissions/e2b2d871-a629-42b8-9ac5-857fb1f3df56

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory
open scoped FourierTransform Real Topology
open SpherePacking SpherePacking.Alternative


theorem solution
    {d : ℕ} {f : Schwartz d}
    (_hf : IsUnrestrictedAdmissible f) :
    quotient (radialSymmetrization f) = quotient f := by
  unfold SpherePacking.Alternative.quotient
  rw [radialSymmetrization_apply, radialSymmetrizationAverage_zero,
    radialSymmetrizationAverage_fourier_zero
      (radialSymmetrization_fourier_average_apply_for_admissibility f)]

