-- Prove2me | solution 1 for SoficGroups.LeavittElementaryMorita.alphaZeroPrefixElementaryGroup_hasPropertyT_of_nine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/0c71bfd4-7c89-4169-9799-62cd18db0e5d

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_hasPropertyT_of_mulEquiv
import Theorems.Thm_SoficGroups_LeavittElementaryMorita_binaryLeavittElementaryThree_hasPropertyT_of_nine

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
universe u₁ u₂ u₃
open SoficGroups.LeavittElementaryMorita
open scoped BigOperators commutatorElement
namespace SoficGroups.LeavittElementaryMorita
theorem _root_.solution
    [HasPropertyT.{0, v} (binaryLeavittElementaryGroup 9)] :
    HasPropertyT.{0, v} (prefixElementaryGroup alphaZeroPrefixCode) := by
  letI : HasPropertyT.{0, v} (binaryLeavittElementaryGroup 3) :=
    binaryLeavittElementaryThree_hasPropertyT_of_nine
  exact hasPropertyT_of_mulEquiv
    (binaryPrefixElementaryGroupEquiv alphaZeroPrefixCode)
end SoficGroups.LeavittElementaryMorita
