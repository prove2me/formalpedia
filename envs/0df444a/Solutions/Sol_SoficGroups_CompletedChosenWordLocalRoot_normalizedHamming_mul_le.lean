-- Prove2me | solution 1 for SoficGroups.CompletedChosenWordLocalRoot.normalizedHamming_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/fda48326-88d0-41bc-bb98-71e270e00dd6

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_normalizedHamming_triangle
import Theorems.Thm_SoficGroups_normalizedHamming_mul_left
import Theorems.Thm_SoficGroups_normalizedHamming_mul_right

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CompletedChosenWordLocalRoot
open Filter Topology
open scoped BigOperators
namespace SoficGroups.CompletedChosenWordLocalRoot
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (p p' q q' : Equiv.Perm V) :
    SoficGroups.normalizedHamming (p * q) (p' * q') ≤
      SoficGroups.normalizedHamming p p' +
        SoficGroups.normalizedHamming q q' := by
  calc
    SoficGroups.normalizedHamming (p * q) (p' * q') ≤
        SoficGroups.normalizedHamming (p * q) (p' * q) +
          SoficGroups.normalizedHamming (p' * q) (p' * q') :=
      SoficGroups.normalizedHamming_triangle _ _ _
    _ = SoficGroups.normalizedHamming p p' +
        SoficGroups.normalizedHamming q q' := by
      rw [SoficGroups.normalizedHamming_mul_right,
        SoficGroups.normalizedHamming_mul_left]
end SoficGroups.CompletedChosenWordLocalRoot
