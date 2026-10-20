-- Prove2me | solution 2 for SpherePacking.CohnElkies.origin_character_sum_norm_sq_eq_orbit_count_sq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:00:12.064423+00:00
-- url     : https://prove2.me/submissions/77c61abf-15cf-4daf-88e4-326104830f59

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped Real
open scoped SchwartzMap FourierTransform
open SpherePacking SpherePacking.CohnElkies


theorem solution {d : ℕ} (P : PeriodicSpherePacking d)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hd : 0 < d) (hD_isBounded : Bornology.IsBounded D) :
    norm (∑' x : ↑(P.centers ∩ D),
        Complex.exp (2 * π * Complex.I *
          ⟪(x : EuclideanSpace ℝ (Fin d)),
            (0 : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) ^ 2
      =
      (P.boundedCenterRepresentativeCount hd hD_isBounded : ℝ) ^ 2 := by
  letI := P.instFintypeBoundedCenterRepresentatives hd hD_isBounded
  rw [tsum_fintype]
  have h0 : ∀ b : ↑(P.centers ∩ D), Complex.exp (2 * π * Complex.I *
      ⟪(b : EuclideanSpace ℝ (Fin d)), (0 : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) = 1 := by
    intro b
    simp
  rw [Finset.sum_congr rfl (fun b _ => h0 b), Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  unfold PeriodicSpherePacking.boundedCenterRepresentativeCount
  simp

