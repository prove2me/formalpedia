-- Prove2me | solution 1 for PeriodicSpherePacking.center_representatives_cover_uniquely
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/432d7525-4da7-4146-ac72-0651526d4b99

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
namespace PeriodicSpherePacking
theorem _root_.solution (S : PeriodicSpherePacking d)
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) :
    ∀ x : S.centers, ∃! g : S.lattice,
      (g +ᵥ x : EuclideanSpace ℝ (Fin d)) ∈ S.centers ∩ D := by
  intro x
  obtain ⟨g, hg, hunique⟩ := hD_unique_covers (x : EuclideanSpace ℝ (Fin d))
  refine ⟨g, ⟨?_, hg⟩, ?_⟩
  · exact S.lattice_action g.property x.property
  · intro h hh
    exact hunique h hh.2
end PeriodicSpherePacking
