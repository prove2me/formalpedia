-- Prove2me | solution 1 for SoficGroups.SourceGeneration.wordT_mul_prefixTable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/3a842156-4a39-4db9-a674-d952b1684223

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
    leavittWordT (target.word i) * prefixTable source target =
      leavittWordT (source.word i) := by
  calc
    leavittWordT (target.word i) * prefixTable source target =
        ∑ j, (leavittWordT (target.word i) *
          leavittWordS (target.word j)) * leavittWordT (source.word j) := by
            simp [prefixTable, Finset.mul_sum, mul_assoc]
    _ = leavittWordT (source.word i) := by
      simp [binaryPrefixCode_orthogonal]
end SoficGroups.SourceGeneration
