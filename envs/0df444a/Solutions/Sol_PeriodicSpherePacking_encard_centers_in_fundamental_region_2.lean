-- Prove2me | solution 2 for PeriodicSpherePacking.encard_centers_in_fundamental_region
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:00:45.139419+00:00
-- url     : https://prove2.me/submissions/cbadb9a9-2ac8-4211-8d4e-473c0aa1a146

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


theorem solution
    (hD_isBounded : IsBounded D)
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D)
    (hd : 0 < d) :
    (S.centers ∩ D).encard = S.centerOrbitCardinality := by
  rw [Set.encard, ← ENat.card_congr (S.centerOrbitEquivFundamentalRegion D hD_unique_covers),
    PeriodicSpherePacking.centerOrbitCardinality, ENat.card_eq_coe_fintype_card]

