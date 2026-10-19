-- Prove2me | solution 2 for PackingBounds.exists_radial_admissible_of_full
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:19:27.42482+00:00
-- url     : https://prove2.me/submissions/3ecce90e-1002-44a3-bf0c-9fbbfb1dcdcf

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
    ∃ g : CohnElkies.Admissible d,
      CohnElkies.quotient g = fullQuotient f := by
  refine ⟨f.radialization, ?_⟩
  show (SpherePacking.Alternative.radialSymmetrization f.function 0).re /
      ((𝓕 (SpherePacking.Alternative.radialSymmetrization f.function)) 0).re = fullQuotient f
  rw [SpherePacking.Alternative.radialSymmetrization_apply,
    SpherePacking.Alternative.radialSymmetrizationAverage_zero,
    SpherePacking.Alternative.radialSymmetrization_fourier_average_apply_for_admissibility,
    SpherePacking.Alternative.radialSymmetrizationAverage_zero]
  rfl

