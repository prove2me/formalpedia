-- Prove2me | solution 1 for PeriodicSpherePacking.card_centers_in_fundamental_region
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/dc55dff8-9d6d-40c4-9acc-2b7e9cf20459

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise
open Finset Set
variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))
namespace PeriodicSpherePacking
theorem _root_.solution
    (hD_isBounded : IsBounded D)
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D)
    (hd : 0 < d) :
    haveI := @Fintype.ofFinite _ <| finite_centers_in_bounded_region S D hD_isBounded hd
    (S.centers ∩ D).toFinset.card = S.centerOrbitCardinality := by
  rw [centerOrbitCardinality]
  convert! Finset.card_eq_of_equiv_fintype ?_
  simpa [Set.mem_toFinset] using! (S.centerOrbitEquivFundamentalRegion D hD_unique_covers).symm
end PeriodicSpherePacking
