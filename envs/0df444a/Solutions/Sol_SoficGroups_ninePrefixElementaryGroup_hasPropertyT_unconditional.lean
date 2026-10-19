-- Prove2me | solution 1 for SoficGroups.ninePrefixElementaryGroup_hasPropertyT_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/187b1755-d8e9-4b81-8ae4-ede6188973da

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_hasPropertyT_of_mulEquiv
import Theorems.Thm_SoficGroups_binaryLeavittElementaryNine_hasPropertyT_unconditional

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators
namespace SoficGroups
theorem _root_.solution :
    HasPropertyT.{0, vSharp} (prefixElementaryGroup ninePrefixCode) := by
  letI : HasPropertyT.{0, vSharp} (binaryLeavittElementaryGroup 9) :=
    binaryLeavittElementaryNine_hasPropertyT_unconditional
  exact hasPropertyT_of_mulEquiv ninePrefixElementaryGroupEquiv
end SoficGroups
