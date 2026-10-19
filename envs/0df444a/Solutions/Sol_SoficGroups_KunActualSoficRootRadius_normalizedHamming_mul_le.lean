-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.normalizedHamming_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/4725db9e-99f2-416b-9d59-7c04fb2a948a

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_normalizedHamming_triangle
import Theorems.Thm_SoficGroups_normalizedHamming_mul_left
import Theorems.Thm_SoficGroups_normalizedHamming_mul_right

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSoficRootRadius
open Filter Topology
open scoped BigOperators Pointwise
namespace SoficGroups.KunActualSoficRootRadius
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
end SoficGroups.KunActualSoficRootRadius
