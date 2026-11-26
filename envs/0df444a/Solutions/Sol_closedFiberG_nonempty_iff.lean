-- Prove2me | solution 1 for closedFiberG_nonempty_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:01:48.420327+00:00
-- url     : https://prove2.me/submissions/fda24630-101e-4a42-bc06-57c361ab53b1

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree

set_option autoImplicit false
open Set Topology MeasureTheory
open scoped Classical
noncomputable section
variable {X : Type*} [TopologicalSpace X]
omit [TopologicalSpace X]
theorem _root_.solution (F : Set (X × (ℕ → ℕ))) (x : X) :
    (closedFiberG F x).Nonempty ↔ x ∈ Prod.fst '' F := by
  constructor
  · rintro ⟨y, hy⟩; exact ⟨(x, y), hy, rfl⟩
  · rintro ⟨⟨x', y⟩, hm, hx⟩; simp at hx; exact ⟨y, hx ▸ hm⟩
