-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.isOpen_extend_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:58:00.888197+00:00
-- url     : https://prove2.me/submissions/795e2d06-faba-449d-881f-f6e28f8480b8

import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.Basic
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_extend

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
open TopologicalSpace
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) (k : ℕ) :
    IsOpen {y : Y | k ∈ extend (Y := Y) (X := X) f y} := by
  have : {y : Y | k ∈ extend (Y := Y) (X := X) f y} =
      ⋃ U ∈ {U : Set Y | IsOpen U ∧ ∀ x : X, ↑x ∈ U → k ∈ f x}, U := by
    ext y
    constructor
    · intro hy
      obtain ⟨U, hU, hyU, hall⟩ := (mem_extend f).mp hy
      exact Set.mem_iUnion₂.mpr ⟨U, ⟨hU, hall⟩, hyU⟩
    · intro hy
      obtain ⟨U, hU, hyU⟩ := Set.mem_iUnion₂.mp hy
      exact (mem_extend f).mpr ⟨U, hU.1, hyU, hU.2⟩
  rw [this]
  exact isOpen_biUnion fun _ hU => hU.1
end Scott1976.DataTypesAsLattices
