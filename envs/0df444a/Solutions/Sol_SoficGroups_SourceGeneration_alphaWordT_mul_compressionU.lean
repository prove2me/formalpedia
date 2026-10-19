-- Prove2me | solution 1 for SoficGroups.SourceGeneration.alphaWordT_mul_compressionU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/9adae5cb-b48a-4168-9c05-ba9889142251

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
    leavittWordT (alphaWord i) * (compressionU : BinaryLeavitt) =
      leavittS 0 * leavittWordT (alphaWord i) +
        leavittS 1 * leavittWordT (betaWord i) := by
  calc
    leavittWordT (alphaWord i) * (compressionU : BinaryLeavitt) =
        (leavittS 0 * leavittWordT (alphaWord i ++ [0]) +
          leavittS 1 * leavittWordT (alphaWord i ++ [1])) *
          (compressionU : BinaryLeavitt) :=
      congrArg (· * (compressionU : BinaryLeavitt))
        (leavittWordT_split (alphaWord i))
    _ = leavittS 0 * (leavittWordT (alphaWord i ++ [0]) *
          prefixTable ninePrefixCode uPrefixCode) +
        leavittS 1 * (leavittWordT (alphaWord i ++ [1]) *
          prefixTable ninePrefixCode uPrefixCode) := by
            change
              (leavittS 0 * leavittWordT (alphaWord i ++ [0]) +
                leavittS 1 * leavittWordT (alphaWord i ++ [1])) *
                prefixTable ninePrefixCode uPrefixCode = _
            simp [add_mul, mul_assoc]
    _ = leavittS 0 * leavittWordT (alphaWord i) +
        leavittS 1 * leavittWordT (betaWord i) := by
          simpa only [ninePrefixCode, uPrefixCode, nineWord_alphaNineIndex,
            nineWord_betaNineIndex, uWord_alphaNineIndex, uWord_betaNineIndex]
            using congrArg₂ (· + ·)
              (congrArg (leavittS 0 * ·)
                (wordT_mul_prefixTable ninePrefixCode uPrefixCode
                  (alphaNineIndex i)))
              (congrArg (leavittS 1 * ·)
                (wordT_mul_prefixTable ninePrefixCode uPrefixCode
                  (betaNineIndex i)))
end SoficGroups.SourceGeneration
