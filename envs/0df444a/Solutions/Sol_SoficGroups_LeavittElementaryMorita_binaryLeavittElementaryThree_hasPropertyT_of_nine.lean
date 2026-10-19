-- Prove2me | solution 1 for SoficGroups.LeavittElementaryMorita.binaryLeavittElementaryThree_hasPropertyT_of_nine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/7eab2aff-8d9a-4403-a3c0-6105a5265dda

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_hasPropertyT_of_mulEquiv

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
    HasPropertyT.{0, v} (binaryLeavittElementaryGroup 3) :=
  hasPropertyT_of_mulEquiv binaryLeavittElementaryThreeEquivNine.symm
end SoficGroups.LeavittElementaryMorita
