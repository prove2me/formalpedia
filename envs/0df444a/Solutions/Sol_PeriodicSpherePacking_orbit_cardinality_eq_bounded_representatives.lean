-- Prove2me | solution 1 for PeriodicSpherePacking.orbit_cardinality_eq_bounded_representatives
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/42e9d5b4-d2f2-4f11-bc05-00c7e32dce8e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PeriodicSpherePacking_card_centers_in_fundamental_region

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
variable {d : ℕ}
namespace PeriodicSpherePacking
theorem _root_.solution (S : PeriodicSpherePacking d) (hd : 0 < d)
  {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
  (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) :
  S.centerOrbitCardinality = S.boundedCenterRepresentativeCount hd hD_isBounded := by
  simpa [PeriodicSpherePacking.boundedCenterRepresentativeCount, Set.toFinset_card] using!
    (S.card_centers_in_fundamental_region (D := D) hD_isBounded hD_unique_covers hd).symm
end PeriodicSpherePacking
