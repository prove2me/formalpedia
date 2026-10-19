-- Prove2me | solution 1 for SoficGroups.alphaPrefixElementaryGroup_hasPropertyT_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/2045e1e7-fd2f-4ed3-add5-9a3adae92900

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_LeavittElementaryMorita_alphaPrefixElementaryGroup_hasPropertyT_of_nine
import Theorems.Thm_SoficGroups_binaryLeavittElementaryNine_hasPropertyT_unconditional

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators
namespace SoficGroups
theorem _root_.solution :
    HasPropertyT.{0, vSharp} (prefixElementaryGroup alphaPrefixCode) := by
  letI : HasPropertyT.{0, vSharp} (binaryLeavittElementaryGroup 9) :=
    binaryLeavittElementaryNine_hasPropertyT_unconditional
  exact LeavittElementaryMorita.alphaPrefixElementaryGroup_hasPropertyT_of_nine
end SoficGroups
