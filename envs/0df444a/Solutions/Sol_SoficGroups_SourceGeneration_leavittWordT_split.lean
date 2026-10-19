-- Prove2me | solution 1 for SoficGroups.SourceGeneration.leavittWordT_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/40a7b0db-ae0c-4b4e-af11-712674cc422c

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
    leavittWordT a =
      leavittS 0 * leavittWordT (a ++ [0]) +
        leavittS 1 * leavittWordT (a ++ [1]) := by
  calc
    leavittWordT a =
        (leavittS 0 * leavittT 0 + leavittS 1 * leavittT 1) *
          leavittWordT a := by
            rw [leavitt_partition]
            simp
    _ = leavittS 0 * leavittWordT (a ++ [0]) +
        leavittS 1 * leavittWordT (a ++ [1]) := by
          simp [leavittWordT_append, leavittWordT, add_mul, mul_assoc]
end SoficGroups.SourceGeneration
