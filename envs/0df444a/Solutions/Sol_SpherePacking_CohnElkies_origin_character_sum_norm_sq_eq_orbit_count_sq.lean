-- Prove2me | solution 1 for SpherePacking.CohnElkies.origin_character_sum_norm_sq_eq_orbit_count_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/708eb7ba-b639-404b-9603-a0ac305baf0b

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped Real
open scoped SchwartzMap FourierTransform
open SpherePacking SpherePacking.CohnElkies
namespace SpherePacking.CohnElkies
theorem _root_.solution {d : ℕ} (P : PeriodicSpherePacking d)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hd : 0 < d) (hD_isBounded : Bornology.IsBounded D) :
    norm (∑' x : ↑(P.centers ∩ D),
        Complex.exp (2 * π * Complex.I *
          ⟪(x : EuclideanSpace ℝ (Fin d)),
            (0 : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2
      =
      (P.boundedCenterRepresentativeCount hd hD_isBounded : ℝ) ^ 2 := by
  letI := P.instFintypeBoundedCenterRepresentatives hd hD_isBounded
  simp [PeriodicSpherePacking.boundedCenterRepresentativeCount]
end SpherePacking.CohnElkies
