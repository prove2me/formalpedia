-- Prove2me | solution 1 for SoficGroups.binaryLeavittEL3_infinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/356caaf9-b682-48ab-80fb-9bfe64b35678

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_elementaryGroup_infinite

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution :
    Infinite (binaryLeavittElementaryGroup 3) :=
  elementaryGroup_infinite (R := BinaryLeavitt)
    (0 : Fin 3) (1 : Fin 3) (by decide)
end SoficGroups
