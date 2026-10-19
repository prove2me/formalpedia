-- Prove2me | solution 1 for SoficGroups.SourceGeneration.prefixTable_mul_wordS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/e14751b5-8dd4-42a6-9e54-d80b11ee36ea

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
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (source target : BinaryPrefixCode ι) (i : ι) :
    prefixTable source target * leavittWordS (source.word i) =
      leavittWordS (target.word i) := by
  calc
    prefixTable source target * leavittWordS (source.word i) =
        ∑ j, leavittWordS (target.word j) *
          (leavittWordT (source.word j) * leavittWordS (source.word i)) := by
            simp [prefixTable, Finset.sum_mul, mul_assoc]
    _ = leavittWordS (target.word i) := by
      simp [binaryPrefixCode_orthogonal]
end SoficGroups.SourceGeneration
