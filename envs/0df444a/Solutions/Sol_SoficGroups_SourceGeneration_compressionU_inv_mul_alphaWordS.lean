-- Prove2me | solution 1 for SoficGroups.SourceGeneration.compressionU_inv_mul_alphaWordS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/b43dbaed-011b-4a0a-80b8-ee03f058d17e

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceGeneration_prefixTable_mul_wordS
import Theorems.Thm_SoficGroups_SourceGeneration_leavittWordS_split

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.SourceGeneration
open scoped commutatorElement
namespace SoficGroups.SourceGeneration
theorem _root_.solution (i : Fin 3) :
    (↑(compressionU⁻¹) : BinaryLeavitt) * leavittWordS (alphaWord i) =
      leavittWordS (alphaWord i) * leavittT 0 +
        leavittWordS (betaWord i) * leavittT 1 := by
  calc
    (↑(compressionU⁻¹) : BinaryLeavitt) * leavittWordS (alphaWord i) =
        (↑(compressionU⁻¹) : BinaryLeavitt) *
          (leavittWordS (alphaWord i ++ [0]) * leavittT 0 +
            leavittWordS (alphaWord i ++ [1]) * leavittT 1) :=
      congrArg ((↑(compressionU⁻¹) : BinaryLeavitt) * ·)
        (leavittWordS_split (alphaWord i))
    _ = (prefixTable uPrefixCode ninePrefixCode *
          leavittWordS (alphaWord i ++ [0])) * leavittT 0 +
        (prefixTable uPrefixCode ninePrefixCode *
          leavittWordS (alphaWord i ++ [1])) * leavittT 1 := by
            change
              prefixTable uPrefixCode ninePrefixCode *
                  (leavittWordS (alphaWord i ++ [0]) * leavittT 0 +
                    leavittWordS (alphaWord i ++ [1]) * leavittT 1) = _
            simp [mul_add, mul_assoc]
    _ = leavittWordS (alphaWord i) * leavittT 0 +
        leavittWordS (betaWord i) * leavittT 1 := by
          simpa only [ninePrefixCode, uPrefixCode, nineWord_alphaNineIndex,
            nineWord_betaNineIndex, uWord_alphaNineIndex, uWord_betaNineIndex]
            using congrArg₂ (· + ·)
              (congrArg (· * leavittT 0)
                (prefixTable_mul_wordS uPrefixCode ninePrefixCode
                  (alphaNineIndex i)))
              (congrArg (· * leavittT 1)
                (prefixTable_mul_wordS uPrefixCode ninePrefixCode
                  (betaNineIndex i)))
end SoficGroups.SourceGeneration
