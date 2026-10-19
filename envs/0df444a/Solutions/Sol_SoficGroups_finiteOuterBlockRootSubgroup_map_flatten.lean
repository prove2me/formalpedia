-- Prove2me | solution 1 for SoficGroups.finiteOuterBlockRootSubgroup_map_flatten
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/b68d081f-1d92-4933-ae47-9518ef7dc68c

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators
namespace SoficGroups
theorem _root_.solution
    {R : Type*} [Ring R] [Algebra (ZMod 2) R]
    (W : Submodule (ZMod 2) R)
    (i j : Fin 3) (hij : i ≠ j) :
    (finiteOuterBlockRootSubgroup W i j hij).map
      (finiteOuterBlockFlattenHom (R := R)) =
        finiteBlockRootSubgroup W i j hij := by
  change (finiteOuterBlockRootHom W i j hij).range.map
    (finiteOuterBlockFlattenHom (R := R)) =
      (finiteBlockRootHom W i j hij).range
  rw [MonoidHom.map_range]
  rfl
end SoficGroups
