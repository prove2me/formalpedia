-- Prove2me | solution 1 for SoficGroups.SourceGeneration.compressionV_inv_mul_alphaWordS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/b7011c70-3457-47a0-adf3-da1701969e61

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
    (↑(compressionV⁻¹) : BinaryLeavitt) * leavittWordS (alphaWord i) =
      leavittWordS (alphaWord i) * leavittT 0 +
        leavittWordS (nuWord i) * leavittT 1 := by
  calc
    (↑(compressionV⁻¹) : BinaryLeavitt) * leavittWordS (alphaWord i) =
        (↑(compressionV⁻¹) : BinaryLeavitt) *
          (leavittWordS (alphaWord i ++ [0]) * leavittT 0 +
            leavittWordS (alphaWord i ++ [1]) * leavittT 1) :=
      congrArg ((↑(compressionV⁻¹) : BinaryLeavitt) * ·)
        (leavittWordS_split (alphaWord i))
    _ = (prefixTable vPrefixCode ninePrefixCode *
          leavittWordS (alphaWord i ++ [0])) * leavittT 0 +
        (prefixTable vPrefixCode ninePrefixCode *
          leavittWordS (alphaWord i ++ [1])) * leavittT 1 := by
            change
              prefixTable vPrefixCode ninePrefixCode *
                  (leavittWordS (alphaWord i ++ [0]) * leavittT 0 +
                    leavittWordS (alphaWord i ++ [1]) * leavittT 1) = _
            simp [mul_add, mul_assoc]
    _ = leavittWordS (alphaWord i) * leavittT 0 +
        leavittWordS (nuWord i) * leavittT 1 := by
          simpa only [ninePrefixCode, vPrefixCode, nineWord_alphaNineIndex,
            nineWord_nuNineIndex, vWord_alphaNineIndex, vWord_nuNineIndex]
            using congrArg₂ (· + ·)
              (congrArg (· * leavittT 0)
                (prefixTable_mul_wordS vPrefixCode ninePrefixCode
                  (alphaNineIndex i)))
              (congrArg (· * leavittT 1)
                (prefixTable_mul_wordS vPrefixCode ninePrefixCode
                  (nuNineIndex i)))
end SoficGroups.SourceGeneration
