-- Prove2me | solution 1 for SoficGroups.SourceGeneration.leavittWordS_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/47e89f6c-bd04-4917-81e0-fa55c48fb7a4

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.SourceGeneration
open scoped commutatorElement
namespace SoficGroups.SourceGeneration
theorem _root_.solution (a : List (Fin 2)) :
    leavittWordS a =
      leavittWordS (a ++ [0]) * leavittT 0 +
        leavittWordS (a ++ [1]) * leavittT 1 := by
  calc
    leavittWordS a = leavittWordS a *
        (leavittS 0 * leavittT 0 + leavittS 1 * leavittT 1) := by
          rw [leavitt_partition]
          simp
    _ = leavittWordS (a ++ [0]) * leavittT 0 +
        leavittWordS (a ++ [1]) * leavittT 1 := by
          simp [leavittWordS_append, leavittWordS, mul_add, mul_assoc]
end SoficGroups.SourceGeneration
