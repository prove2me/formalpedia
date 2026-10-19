-- Prove2me | solution 1 for SoficGroups.cyclicFiniteBlockRootSubgroup_le_elementaryGroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/c9c16aef-4645-4ec9-85cd-46d9612584fd

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_finiteBlockRootSubgroup_le_elementaryGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u
variable {R : Type u} [Ring R] [Algebra (ZMod 2) R]
namespace SoficGroups
theorem _root_.solution
    (W : Submodule (ZMod 2) R) :
    cyclicFiniteBlockRootSubgroup W ≤ elementaryGroup (Fin 9) R := by
  unfold cyclicFiniteBlockRootSubgroup
  exact sup_le
    (sup_le
      (finiteBlockRootSubgroup_le_elementaryGroup W 0 1 (by decide))
      (finiteBlockRootSubgroup_le_elementaryGroup W 1 2 (by decide)))
    (finiteBlockRootSubgroup_le_elementaryGroup W 2 0 (by decide))
end SoficGroups
