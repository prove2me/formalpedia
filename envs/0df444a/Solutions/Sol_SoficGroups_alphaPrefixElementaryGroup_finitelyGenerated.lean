-- Prove2me | solution 1 for SoficGroups.alphaPrefixElementaryGroup_finitelyGenerated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/c1c8a260-7db6-4de2-834b-acdd0f4bc159

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_binaryLeavittEL3_finitelyGenerated

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution :
    Group.FG (prefixElementaryGroup alphaPrefixCode) := by
  letI : Group.FG (binaryLeavittElementaryGroup 3) :=
    binaryLeavittEL3_finitelyGenerated
  exact Group.fg_of_surjective
    (f := alphaPrefixElementaryGroupEquiv.toMonoidHom)
    alphaPrefixElementaryGroupEquiv.surjective
end SoficGroups
