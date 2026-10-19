-- Prove2me | solution 1 for SoficGroups.finiteBlockRootSubgroup_le_elementaryGroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/2765fa05-72b7-4afb-a358-38b13a28a1fc

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_finiteBlockRootHom_single

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u
variable {R : Type u} [Ring R] [Algebra (ZMod 2) R]
namespace SoficGroups
theorem _root_.solution
    (W : Submodule (ZMod 2) R)
    (i j : Fin 3) (hij : i ≠ j) :
    finiteBlockRootSubgroup W i j hij ≤
      elementaryGroup (Fin 9) R := by
  rintro _ ⟨A, rfl⟩
  change
    finiteBlockRootHom W i j hij
        (Multiplicative.ofAdd A.toAdd) ∈
      elementaryGroup (Fin 9) R
  refine Matrix.induction_on'
    (P := fun M : Matrix (Fin 3) (Fin 3) W =>
      finiteBlockRootHom W i j hij (Multiplicative.ofAdd M) ∈
        elementaryGroup (Fin 9) R)
    A.toAdd ?_ ?_ ?_
  · change finiteBlockRootHom W i j hij 1 ∈ elementaryGroup (Fin 9) R
    rw [map_one]
    exact (elementaryGroup (Fin 9) R).one_mem
  · intro P Q hP hQ
    change
      finiteBlockRootHom W i j hij
          (Multiplicative.ofAdd (P + Q)) ∈
        elementaryGroup (Fin 9) R
    change
      finiteBlockRootHom W i j hij
          (Multiplicative.ofAdd P * Multiplicative.ofAdd Q) ∈
        elementaryGroup (Fin 9) R
    rw [map_mul]
    exact (elementaryGroup (Fin 9) R).mul_mem hP hQ
  · intro p q a
    rw [finiteBlockRootHom_single]
    exact elementaryUnit_mem _ _ _ (a : R)
end SoficGroups
