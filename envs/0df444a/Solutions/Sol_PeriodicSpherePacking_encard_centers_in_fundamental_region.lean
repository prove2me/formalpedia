-- Prove2me | solution 1 for PeriodicSpherePacking.encard_centers_in_fundamental_region
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/279ec580-a555-43fc-bfde-9fe1b6514f9f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_PeriodicSpherePacking_card_centers_in_fundamental_region

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
    (S.centers ∩ D).encard = S.centerOrbitCardinality := by
  rw [← S.card_centers_in_fundamental_region D hD_isBounded hD_unique_covers hd]
  convert! Set.encard_eq_coe_toFinset_card _
end PeriodicSpherePacking
