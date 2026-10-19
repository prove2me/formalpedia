-- Prove2me | solution 1 for SoficGroups.finiteOuterBlockProductCentralRoot_pair_le_centralizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/5372aa0c-25cb-4b4e-a896-5048fe5735fa

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_finiteOuterBlockProductCentralRoot_commute_left
import Theorems.Thm_SoficGroups_finiteOuterBlockProductCentralRoot_commute_right

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]
namespace SoficGroups
theorem _root_.solution
    (W : Submodule (ZMod 2) R)
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (B : Matrix (Fin 3) (Fin 3) W) :
    finiteOuterBlockRootSubgroup W i j hij ⊔
      finiteOuterBlockRootSubgroup W j k hjk ≤
      Subgroup.centralizer
        (finiteOuterBlockProductCentralRootSubgroup W i k hik B :
          Set (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R))) := by
  apply sup_le
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (finiteOuterBlockProductCentralRoot_commute_left
      W i j k hij hik B x z hx hz).symm.eq
  · intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (finiteOuterBlockProductCentralRoot_commute_right
      W i j k hjk hik B y z hy hz).symm.eq
end SoficGroups
