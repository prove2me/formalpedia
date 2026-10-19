-- Prove2me | solution 1 for PeriodicConstantApprox.boundary_count_mul_ball_volume_le_shell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:36.514984+00:00
-- url     : https://prove2.me/submissions/ecb719ca-605a-4efb-b8c7-20c4d84e17ac

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PeriodicConstantApprox_boundary_count_mul_ball_volume_le_annulus

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise Topology
variable {d : ℕ}
open PeriodicConstantApprox
open Filter
variable {d : ℕ}
open scoped ENNReal Pointwise BigOperators
open SpherePacking EuclideanSpace MeasureTheory Metric
variable {d : ℕ}
variable (S : SpherePacking d)
namespace PeriodicConstantApprox
theorem _root_.solution {L : ℝ} (hL : 0 < L)
    (hSsep : S.separation = 1)
    {g : axisCellLattice (d := d) L hL} {s : Finset (EuclideanSpace ℝ (Fin d))}
    (hs_centers : ∀ x ∈ s, x ∈ S.centers)
    (hs_boundary : ∀ x ∈ s,
      x ∈ (g +ᵥ axisAlignedCell (d := d) L) \ (g +ᵥ insetAxisAlignedCell (d := d) L (1 / 2))) :
    (s.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ)) ≤
      volume (((uniformShellShift d (- (1 / 2 : ℝ))) +ᵥ insetAxisAlignedCell (d := d) (L + 1) 0) \
          insetAxisAlignedCell (d := d) L 1) := by simpa [uniformShellShift, constantCoordinateVector] using!
    (boundary_count_mul_ball_volume_le_annulus (S := S) hL hSsep hs_centers hs_boundary)
end PeriodicConstantApprox
