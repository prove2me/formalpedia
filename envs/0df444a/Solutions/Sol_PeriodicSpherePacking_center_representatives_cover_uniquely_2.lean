-- Prove2me | solution 2 for PeriodicSpherePacking.center_representatives_cover_uniquely
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:24:14.342799+00:00
-- url     : https://prove2.me/submissions/1db0b51d-272c-41dd-9bd5-45e3b4c2fd4c

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
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) :
    ∀ x : S.centers, ∃! g : S.lattice,
      (g +ᵥ x : EuclideanSpace ℝ (Fin d)) ∈ S.centers ∩ D := by
  intro x
  obtain ⟨g, hg, huniq⟩ := hD_unique_covers (x : EuclideanSpace ℝ (Fin d))
  refine ⟨g, ⟨?_, ?_⟩, fun g' hg' => huniq g' ?_⟩
  · first
      | exact (g +ᵥ x).2
      | exact S.lattice_action g.2 x.2
  · exact hg
  · exact hg'.2

