-- Prove2me | solution 1 for SoficGroups.elementaryUnit_mem_finiteBlockRootSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/095bc835-8a49-4ac3-9e8f-c8ab666b49f6

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
    (i j : Fin 3) (hij : i ≠ j) (p q : Fin 3)
    (a : R) (ha : a ∈ W) :
    elementaryUnit (finiteBlockIndex i p) (finiteBlockIndex j q)
        (finiteBlockIndex_ne_of_ne hij p q) a ∈
      finiteBlockRootSubgroup W i j hij := by
  refine ⟨Multiplicative.ofAdd (Matrix.single p q (⟨a, ha⟩ : W)), ?_⟩
  exact finiteBlockRootHom_single W i j hij p q ⟨a, ha⟩
end SoficGroups
