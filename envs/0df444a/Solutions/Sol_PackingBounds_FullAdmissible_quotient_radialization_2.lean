-- Prove2me | solution 2 for PackingBounds.FullAdmissible.quotient_radialization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:18:52.228732+00:00
-- url     : https://prove2.me/submissions/3e3efc2d-b235-4ca3-9129-ebde94c61ed3

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
open Filter
open scoped FourierTransform SchwartzMap Topology
open PackingBounds


theorem solution {d : ℕ}
    (f : FullAdmissible d) :
    CohnElkies.quotient f.radialization = fullQuotient f := by
  show (SpherePacking.Alternative.radialSymmetrization f.function 0).re /
      ((𝓕 (SpherePacking.Alternative.radialSymmetrization f.function)) 0).re = fullQuotient f
  rw [SpherePacking.Alternative.radialSymmetrization_apply,
    SpherePacking.Alternative.radialSymmetrizationAverage_zero,
    SpherePacking.Alternative.radialSymmetrization_fourier_average_apply_for_admissibility,
    SpherePacking.Alternative.radialSymmetrizationAverage_zero]
  rfl

