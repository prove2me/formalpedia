-- Prove2me | solution 1 for SoficGroups.SourceGeneration.alphaWordT_mul_compressionV
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/69f5e9da-959d-4159-8c66-b70a682d5f4c

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceGeneration_wordT_mul_prefixTable
import Theorems.Thm_SoficGroups_SourceGeneration_leavittWordT_split

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
    leavittWordT (alphaWord i) * (compressionV : BinaryLeavitt) =
      leavittS 0 * leavittWordT (alphaWord i) +
        leavittS 1 * leavittWordT (nuWord i) := by
  calc
    leavittWordT (alphaWord i) * (compressionV : BinaryLeavitt) =
        (leavittS 0 * leavittWordT (alphaWord i ++ [0]) +
          leavittS 1 * leavittWordT (alphaWord i ++ [1])) *
          (compressionV : BinaryLeavitt) :=
      congrArg (· * (compressionV : BinaryLeavitt))
        (leavittWordT_split (alphaWord i))
    _ = leavittS 0 * (leavittWordT (alphaWord i ++ [0]) *
          prefixTable ninePrefixCode vPrefixCode) +
        leavittS 1 * (leavittWordT (alphaWord i ++ [1]) *
          prefixTable ninePrefixCode vPrefixCode) := by
            change
              (leavittS 0 * leavittWordT (alphaWord i ++ [0]) +
                leavittS 1 * leavittWordT (alphaWord i ++ [1])) *
                prefixTable ninePrefixCode vPrefixCode = _
            simp [add_mul, mul_assoc]
    _ = leavittS 0 * leavittWordT (alphaWord i) +
        leavittS 1 * leavittWordT (nuWord i) := by
          simpa only [ninePrefixCode, vPrefixCode, nineWord_alphaNineIndex,
            nineWord_nuNineIndex, vWord_alphaNineIndex, vWord_nuNineIndex]
            using congrArg₂ (· + ·)
              (congrArg (leavittS 0 * ·)
                (wordT_mul_prefixTable ninePrefixCode vPrefixCode
                  (alphaNineIndex i)))
              (congrArg (leavittS 1 * ·)
                (wordT_mul_prefixTable ninePrefixCode vPrefixCode
                  (nuNineIndex i)))
end SoficGroups.SourceGeneration
