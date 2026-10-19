-- Prove2me | solution 1 for SoficGroups.elementaryUnit_mem_cyclicFiniteBlockRootSubgroup_of_block_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/fdbd63d4-5ead-4990-a5ed-0585ab0d72e7

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_elementaryUnit_mem_finiteBlockRootSubgroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u
variable {R : Type u} [Ring R] [Algebra (ZMod 2) R]
namespace SoficGroups
theorem _root_.solution
    (W : Submodule (ZMod 2) R) (hW : (1 : R) ∈ W)
    (i j : Fin 3) (hij : i ≠ j) (p q : Fin 3)
    (a : R) (ha : a ∈ W) :
    elementaryUnit (finiteBlockIndex i p) (finiteBlockIndex j q)
        (finiteBlockIndex_ne_of_ne hij p q) a ∈
      cyclicFiniteBlockRootSubgroup W := by
  let H : Subgroup (Matrix (Fin 9) (Fin 9) R)ˣ :=
    cyclicFiniteBlockRootSubgroup W
  have h01 (p q : Fin 3) (a : R) (ha : a ∈ W) :
      elementaryUnit (finiteBlockIndex 0 p) (finiteBlockIndex 1 q)
          (finiteBlockIndex_ne_of_ne (by decide) p q) a ∈ H := by
    apply (show finiteBlockRootSubgroup W 0 1 (by decide) ≤ H from
      (show finiteBlockRootSubgroup W 0 1 (by decide) ≤
        (finiteBlockRootSubgroup W 0 1 (by decide) ⊔
          finiteBlockRootSubgroup W 1 2 (by decide)) ⊔
          finiteBlockRootSubgroup W 2 0 (by decide) from
        le_trans le_sup_left le_sup_left))
    exact elementaryUnit_mem_finiteBlockRootSubgroup
      W 0 1 (by decide) p q a ha
  have h12 (p q : Fin 3) (a : R) (ha : a ∈ W) :
      elementaryUnit (finiteBlockIndex 1 p) (finiteBlockIndex 2 q)
          (finiteBlockIndex_ne_of_ne (by decide) p q) a ∈ H := by
    apply (show finiteBlockRootSubgroup W 1 2 (by decide) ≤ H from
      (show finiteBlockRootSubgroup W 1 2 (by decide) ≤
        (finiteBlockRootSubgroup W 0 1 (by decide) ⊔
          finiteBlockRootSubgroup W 1 2 (by decide)) ⊔
          finiteBlockRootSubgroup W 2 0 (by decide) from
        le_trans le_sup_right le_sup_left))
    exact elementaryUnit_mem_finiteBlockRootSubgroup
      W 1 2 (by decide) p q a ha
  have h20 (p q : Fin 3) (a : R) (ha : a ∈ W) :
      elementaryUnit (finiteBlockIndex 2 p) (finiteBlockIndex 0 q)
          (finiteBlockIndex_ne_of_ne (by decide) p q) a ∈ H := by
    apply (show finiteBlockRootSubgroup W 2 0 (by decide) ≤ H from
      (show finiteBlockRootSubgroup W 2 0 (by decide) ≤
        (finiteBlockRootSubgroup W 0 1 (by decide) ⊔
          finiteBlockRootSubgroup W 1 2 (by decide)) ⊔
          finiteBlockRootSubgroup W 2 0 (by decide) from le_sup_right))
    exact elementaryUnit_mem_finiteBlockRootSubgroup
      W 2 0 (by decide) p q a ha
  have h02 (p q : Fin 3) (a : R) (ha : a ∈ W) :
      elementaryUnit (finiteBlockIndex 0 p) (finiteBlockIndex 2 q)
          (finiteBlockIndex_ne_of_ne (by decide) p q) a ∈ H :=
    elementaryUnit_mem_of_two_step H
      (finiteBlockIndex 0 p) (finiteBlockIndex 1 0)
      (finiteBlockIndex 2 q)
      (finiteBlockIndex_ne_of_ne (by decide) p 0)
      (finiteBlockIndex_ne_of_ne (by decide) 0 q)
      (finiteBlockIndex_ne_of_ne (by decide) p q) a
      (h01 p 0 a ha) (h12 0 q 1 hW)
  have h10 (p q : Fin 3) (a : R) (ha : a ∈ W) :
      elementaryUnit (finiteBlockIndex 1 p) (finiteBlockIndex 0 q)
          (finiteBlockIndex_ne_of_ne (by decide) p q) a ∈ H :=
    elementaryUnit_mem_of_two_step H
      (finiteBlockIndex 1 p) (finiteBlockIndex 2 0)
      (finiteBlockIndex 0 q)
      (finiteBlockIndex_ne_of_ne (by decide) p 0)
      (finiteBlockIndex_ne_of_ne (by decide) 0 q)
      (finiteBlockIndex_ne_of_ne (by decide) p q) a
      (h12 p 0 a ha) (h20 0 q 1 hW)
  have h21 (p q : Fin 3) (a : R) (ha : a ∈ W) :
      elementaryUnit (finiteBlockIndex 2 p) (finiteBlockIndex 1 q)
          (finiteBlockIndex_ne_of_ne (by decide) p q) a ∈ H :=
    elementaryUnit_mem_of_two_step H
      (finiteBlockIndex 2 p) (finiteBlockIndex 0 0)
      (finiteBlockIndex 1 q)
      (finiteBlockIndex_ne_of_ne (by decide) p 0)
      (finiteBlockIndex_ne_of_ne (by decide) 0 q)
      (finiteBlockIndex_ne_of_ne (by decide) p q) a
      (h20 p 0 a ha) (h01 0 q 1 hW)
  change
    elementaryUnit (finiteBlockIndex i p) (finiteBlockIndex j q)
        (finiteBlockIndex_ne_of_ne hij p q) a ∈ H
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact h01 p q a ha
  · exact h02 p q a ha
  · exact h10 p q a ha
  · exact (hij rfl).elim
  · exact h12 p q a ha
  · exact h20 p q a ha
  · exact h21 p q a ha
  · exact (hij rfl).elim
end SoficGroups
