-- Prove2me | solution 2 for PackingBounds.fullQuotientSet_eq_radial
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:32:39.660999+00:00
-- url     : https://prove2.me/submissions/d43394b8-f0df-42e9-8d45-62948d2cd69b

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


theorem solution (d : ℕ) :
    fullQuotientSet d = CohnElkies.quotientSet d := by
  ext q
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨f.radialization, ?_⟩
    unfold CohnElkies.quotient fullQuotient FullAdmissible.radialization
    simp only
    rw [SpherePacking.Alternative.radialSymmetrization_apply,
      SpherePacking.Alternative.radialSymmetrizationAverage_zero,
      SpherePacking.Alternative.radialSymmetrization_fourier_average_apply_for_admissibility,
      SpherePacking.Alternative.radialSymmetrizationAverage_zero]
  · rintro ⟨f, rfl⟩
    exact ⟨radialToFull f, rfl⟩

