-- Prove2me | solution 1 for SoficGroups.elementaryUnit_mem_cyclicFiniteBlockRootSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/7032de16-a05b-44fe-8f1d-c60e568c1416

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_elementaryUnit_mem_cyclicFiniteBlockRootSubgroup_of_block_ne

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u
variable {R : Type u} [Ring R] [Algebra (ZMod 2) R]
namespace SoficGroups
theorem _root_.solution
    (W : Submodule (ZMod 2) R) (hW : (1 : R) ∈ W)
    (x y : Fin 9) (hxy : x ≠ y) (a : R) (ha : a ∈ W) :
    elementaryUnit x y hxy a ∈ cyclicFiniteBlockRootSubgroup W := by
  obtain ⟨⟨i, p⟩, rfl⟩ :=
    (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).surjective x
  obtain ⟨⟨j, q⟩, rfl⟩ :=
    (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).surjective y
  change
    elementaryUnit (finiteBlockIndex i p) (finiteBlockIndex j q) hxy a ∈
      cyclicFiniteBlockRootSubgroup W
  by_cases hij : i = j
  · subst j
    let k : Fin 3 := i + 1
    have hik : i ≠ k := by
      dsimp [k]
      fin_cases i <;> decide
    exact elementaryUnit_mem_of_two_step
      (cyclicFiniteBlockRootSubgroup W)
      (finiteBlockIndex i p) (finiteBlockIndex k 0)
      (finiteBlockIndex i q)
      (finiteBlockIndex_ne_of_ne hik p 0)
      (finiteBlockIndex_ne_of_ne hik.symm 0 q)
      hxy a
      (elementaryUnit_mem_cyclicFiniteBlockRootSubgroup_of_block_ne
        W hW i k hik p 0 a ha)
      (elementaryUnit_mem_cyclicFiniteBlockRootSubgroup_of_block_ne
        W hW k i hik.symm 0 q 1 hW)
  · exact elementaryUnit_mem_cyclicFiniteBlockRootSubgroup_of_block_ne
      W hW i j hij p q a ha
end SoficGroups
