-- Prove2me | solution 2 for PeriodicSpherePacking.packing_density_zero_of_empty_centers
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:30:10.644991+00:00
-- url     : https://prove2.me/submissions/8ecf9181-63eb-4105-a094-f85b3b78c415

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open Filter
open scoped Pointwise
open scoped Topology
variable {d : ℕ}


theorem solution (S : PeriodicSpherePacking d)
    (hd : 0 < d) [instEmpty : IsEmpty S.centers] : S.upperPackingDensity = 0 := by
  have h : S.toSpherePacking.occupiedBallRegion = ∅ := by
    simp [SpherePacking.occupiedBallRegion]
  unfold SpherePacking.upperPackingDensity SpherePacking.densityInsideRadius
  simp [h]

