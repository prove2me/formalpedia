-- Prove2me | solution 1 for SoficGroups.alphaZeroPrefixElementaryGroup_hasPropertyT_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/ea7c3f21-f819-450d-8ed3-090748ded870

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_LeavittElementaryMorita_alphaZeroPrefixElementaryGroup_hasPropertyT_of_nine
import Theorems.Thm_SoficGroups_binaryLeavittElementaryNine_hasPropertyT_unconditional

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators
namespace SoficGroups
theorem _root_.solution :
    HasPropertyT.{0, vSharp} (prefixElementaryGroup alphaZeroPrefixCode) := by
  letI : HasPropertyT.{0, vSharp} (binaryLeavittElementaryGroup 9) :=
    binaryLeavittElementaryNine_hasPropertyT_unconditional
  exact LeavittElementaryMorita.alphaZeroPrefixElementaryGroup_hasPropertyT_of_nine
end SoficGroups
