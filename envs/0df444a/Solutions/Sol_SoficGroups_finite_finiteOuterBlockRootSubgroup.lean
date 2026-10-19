-- Prove2me | solution 1 for SoficGroups.finite_finiteOuterBlockRootSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/c2dd0f43-a09d-4608-bd75-1f7ad39ca3c1

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]
namespace SoficGroups
theorem _root_.solution
    (W : Submodule (ZMod 2) R) [Finite W]
    (i j : Fin 3) (hij : i ≠ j) :
    Finite (finiteOuterBlockRootSubgroup W i j hij) := by
  let f : Multiplicative (Matrix (Fin 3) (Fin 3) W) →
      finiteOuterBlockRootSubgroup W i j hij :=
    fun x => ⟨finiteOuterBlockRootHom W i j hij x, ⟨x, rfl⟩⟩
  apply Finite.of_surjective f
  intro x
  obtain ⟨a, ha⟩ := x.property
  exact ⟨a, Subtype.ext ha⟩
end SoficGroups
