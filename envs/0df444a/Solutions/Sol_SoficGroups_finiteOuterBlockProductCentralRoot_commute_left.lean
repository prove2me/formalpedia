-- Prove2me | solution 1 for SoficGroups.finiteOuterBlockProductCentralRoot_commute_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/db1ced7a-cfdf-4dda-84ae-06b2bfca864b

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_finiteOuterElementaryRoot_commute_of_nonadjacent

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]
namespace SoficGroups
theorem _root_.solution
    (W : Submodule (ZMod 2) R)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k)
    (B : Matrix (Fin 3) (Fin 3) W)
    (x z : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R))
    (hx : x ∈ finiteOuterBlockRootSubgroup W i j hij)
    (hz : z ∈ finiteOuterBlockProductCentralRootSubgroup W i k hik B) :
    Commute x z := by
  obtain ⟨A, rfl⟩ := hx
  obtain ⟨C, rfl⟩ := hz
  exact finiteOuterElementaryRoot_commute_of_nonadjacent
    i j i k hij hik hij.symm hik.symm
    (finiteBlockCoefficientMatrixHom W A.toAdd)
    (finiteBlockCoefficientMatrixRightMul W B C.toAdd)
end SoficGroups
