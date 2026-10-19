-- Prove2me | solution 1 for SoficGroups.finiteOuterBlockProductCentralRoot_commute_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/7d4006b2-30d3-43f7-bcdd-b081622af122

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
    (i j k : Fin 3) (hjk : j ≠ k) (hik : i ≠ k)
    (B : Matrix (Fin 3) (Fin 3) W)
    (y z : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R))
    (hy : y ∈ finiteOuterBlockRootSubgroup W j k hjk)
    (hz : z ∈ finiteOuterBlockProductCentralRootSubgroup W i k hik B) :
    Commute y z := by
  obtain ⟨A, rfl⟩ := hy
  obtain ⟨C, rfl⟩ := hz
  exact finiteOuterElementaryRoot_commute_of_nonadjacent
    j k i k hjk hik hik.symm hjk.symm
    (finiteBlockCoefficientMatrixHom W A.toAdd)
    (finiteBlockCoefficientMatrixRightMul W B C.toAdd)
end SoficGroups
