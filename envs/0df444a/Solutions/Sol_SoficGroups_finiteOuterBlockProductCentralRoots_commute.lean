-- Prove2me | solution 1 for SoficGroups.finiteOuterBlockProductCentralRoots_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/93f2a361-279a-4349-aa0b-143431f813e6

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_finiteOuterElementaryRoot_commute_same

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]
namespace SoficGroups
theorem _root_.solution
    (W : Submodule (ZMod 2) R)
    (i k : Fin 3) (hik : i ≠ k)
    (B C : Matrix (Fin 3) (Fin 3) W)
    (z w : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R))
    (hz : z ∈ finiteOuterBlockProductCentralRootSubgroup W i k hik B)
    (hw : w ∈ finiteOuterBlockProductCentralRootSubgroup W i k hik C) :
    Commute z w := by
  obtain ⟨A, rfl⟩ := hz
  obtain ⟨D, rfl⟩ := hw
  exact finiteOuterElementaryRoot_commute_same i k hik
    (finiteBlockCoefficientMatrixRightMul W B A.toAdd)
    (finiteBlockCoefficientMatrixRightMul W C D.toAdd)
end SoficGroups
