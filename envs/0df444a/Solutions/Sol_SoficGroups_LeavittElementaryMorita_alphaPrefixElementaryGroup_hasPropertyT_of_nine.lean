-- Prove2me | solution 1 for SoficGroups.LeavittElementaryMorita.alphaPrefixElementaryGroup_hasPropertyT_of_nine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/4de83e13-aefd-4d92-8b9e-e5dd8ecfaa6f

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
    HasPropertyT.{0, v} (prefixElementaryGroup alphaPrefixCode) := by
  letI : HasPropertyT.{0, v} (binaryLeavittElementaryGroup 3) :=
    binaryLeavittElementaryThree_hasPropertyT_of_nine
  exact hasPropertyT_of_mulEquiv alphaPrefixElementaryGroupEquiv
end SoficGroups.LeavittElementaryMorita
