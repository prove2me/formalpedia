-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_1_5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:03:21.605718+00:00
-- url     : https://prove2.me/submissions/9394a6be-c50c-41c5-b99d-ddac566cf6a4

import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.Basic
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Theorems.Thm_Scott1976_DataTypesAsLattices_isOpen_extend_mem

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
open TopologicalSpace
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {Y : Type*} [TopologicalSpace Y] {X : Set Y}
    (f : X → Pomega) : Continuous (extend (Y := Y) (X := X) f) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨k, rfl⟩
  exact isOpen_extend_mem f k
end Scott1976.DataTypesAsLattices
