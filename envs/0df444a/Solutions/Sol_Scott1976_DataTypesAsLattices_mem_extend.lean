-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.mem_extend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:56:07.386707+00:00
-- url     : https://prove2.me/submissions/36dbbd47-7933-4ec1-9c8f-965c7ceea15a

import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.Basic
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
open TopologicalSpace
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) {y : Y} {k : ℕ} :
    k ∈ extend (Y := Y) (X := X) f y ↔
      ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ ∀ x : X, ↑x ∈ U → k ∈ f x := by
  constructor
  · intro hk
    rcases Set.mem_sUnion.mp hk with ⟨t, ⟨U, hU, hy, rfl⟩, hkt⟩
    refine ⟨U, hU, hy, ?_⟩
    intro x hx
    exact Set.mem_sInter.mp hkt (f x) ⟨x, hx, rfl⟩
  · intro ⟨U, hU, hy, hall⟩
    refine Set.mem_sUnion.mpr ⟨⋂₀ (f '' {x : X | ↑x ∈ U}), ⟨U, hU, hy, rfl⟩, ?_⟩
    intro t ht
    rcases ht with ⟨x, hx, rfl⟩
    exact hall x hx
end Scott1976.DataTypesAsLattices
