-- Prove2me | solution 1 for SoficGroups.binaryLeavittEL3_finitelyGenerated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/43b8e8ce-bce0-4713-a7cc-7a0f3f75caee

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_elementaryGroup_three_finitelyGenerated

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution :
    Group.FG (binaryLeavittElementaryGroup 3) :=
  elementaryGroup_three_finitelyGenerated
end SoficGroups
