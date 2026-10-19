-- Prove2me | solution 1 for SoficGroups.SourceGeneration.prefixElementaryEntry_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/8dd34551-bd1e-4f31-b0af-ac221b31e64b

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
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι) (i j k l : ι)
    (a b : BinaryLeavitt) :
    prefixElementaryEntry E i j a * prefixElementaryEntry E k l b =
      if j = k then prefixElementaryEntry E i l (a * b) else 0 := by
  calc
    prefixElementaryEntry E i j a * prefixElementaryEntry E k l b =
        leavittWordS (E.word i) * a *
          (leavittWordT (E.word j) * leavittWordS (E.word k)) *
          b * leavittWordT (E.word l) := by
            simp [prefixElementaryEntry, mul_assoc]
    _ = if j = k then prefixElementaryEntry E i l (a * b) else 0 := by
      rw [binaryPrefixCode_orthogonal E j k]
      split <;> simp [prefixElementaryEntry, mul_assoc]
end SoficGroups.SourceGeneration
