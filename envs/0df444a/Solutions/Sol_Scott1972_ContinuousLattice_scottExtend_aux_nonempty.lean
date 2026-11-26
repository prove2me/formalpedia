-- Prove2me | solution 1 for Scott1972.ContinuousLattice.scottExtend_aux_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:32:09.842668+00:00
-- url     : https://prove2.me/submissions/6e034a79-9cfe-40e7-9683-9dea9aab1337

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions

set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {E : Type*} [CompleteLattice E]
namespace Scott1972.ContinuousLattice
theorem _root_.solution (e : X → Y) (f : X → E) (y : Y) :
    {d | ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ d = sInf (f '' (e ⁻¹' V))}.Nonempty :=
  ⟨_, Set.univ, isOpen_univ, Set.mem_univ y, rfl⟩
end Scott1972.ContinuousLattice
