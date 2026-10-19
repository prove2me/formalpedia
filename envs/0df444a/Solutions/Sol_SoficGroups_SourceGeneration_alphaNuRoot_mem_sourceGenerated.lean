-- Prove2me | solution 1 for SoficGroups.SourceGeneration.alphaNuRoot_mem_sourceGenerated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/db182be6-43b1-44d1-a802-6a1d04d3c0b8

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceGeneration_alphaRoot_mem_sourceGenerated
import Theorems.Thm_SoficGroups_SourceGeneration_compressionV_mem_sourceGenerated
import Theorems.Thm_SoficGroups_SourceGeneration_binaryBlockSandwich
import Theorems.Thm_SoficGroups_SourceGeneration_compressionV_inv_mul_alphaWordS
import Theorems.Thm_SoficGroups_SourceGeneration_alphaWordT_mul_compressionV

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.SourceGeneration
open scoped commutatorElement
namespace SoficGroups.SourceGeneration
theorem _root_.solution
    (i j : Fin 3) (hij : i ≠ j) (p q : Fin 2) (a : BinaryLeavitt) :
    prefixElementaryUnit ninePrefixCode
      (alphaNuNineIndex p i) (alphaNuNineIndex q j)
      (alphaNuNineIndex_ne hij p q) a ∈ sourceGeneratedGroup := by
  have hα := alphaRoot_mem_sourceGenerated i j hij
    (leavittS p * a * leavittT q)
  have hV := compressionV_mem_sourceGenerated
  have hconj :
      compressionV⁻¹ *
        prefixElementaryUnit alphaPrefixCode i j hij
          (leavittS p * a * leavittT q) * compressionV ∈
        sourceGeneratedGroup :=
    sourceGeneratedGroup.mul_mem
      (sourceGeneratedGroup.mul_mem (sourceGeneratedGroup.inv_mem hV) hα) hV
  have heq :
      compressionV⁻¹ *
        prefixElementaryUnit alphaPrefixCode i j hij
          (leavittS p * a * leavittT q) * compressionV =
        prefixElementaryUnit ninePrefixCode
          (alphaNuNineIndex p i) (alphaNuNineIndex q j)
          (alphaNuNineIndex_ne hij p q) a := by
    apply Units.ext
    change
      (↑(compressionV⁻¹) : BinaryLeavitt) *
          (1 + leavittWordS (alphaWord i) *
            (leavittS p * a * leavittT q) *
            leavittWordT (alphaWord j)) *
          (compressionV : BinaryLeavitt) =
        1 + leavittWordS (nineWord (alphaNuNineIndex p i)) * a *
          leavittWordT (nineWord (alphaNuNineIndex q j))
    calc
      (↑(compressionV⁻¹) : BinaryLeavitt) *
          (1 + leavittWordS (alphaWord i) *
            (leavittS p * a * leavittT q) *
            leavittWordT (alphaWord j)) *
          (compressionV : BinaryLeavitt) =
        1 + ((↑(compressionV⁻¹) : BinaryLeavitt) *
            leavittWordS (alphaWord i)) *
          (leavittS p * a * leavittT q) *
          (leavittWordT (alphaWord j) * (compressionV : BinaryLeavitt)) := by
            simp [mul_add, add_mul, mul_assoc]
      _ = 1 +
          (leavittWordS (alphaWord i) * leavittT 0 +
            leavittWordS (nuWord i) * leavittT 1) *
          (leavittS p * a * leavittT q) *
          (leavittS 0 * leavittWordT (alphaWord j) +
            leavittS 1 * leavittWordT (nuWord j)) := by
              rw [compressionV_inv_mul_alphaWordS,
                alphaWordT_mul_compressionV]
      _ = 1 + leavittWordS (nineWord (alphaNuNineIndex p i)) * a *
          leavittWordT (nineWord (alphaNuNineIndex q j)) := by
            rw [binaryBlockSandwich]
            simp only [nineWord_alphaNuNineIndex]
            split_ifs <;> rfl
  exact heq ▸ hconj
end SoficGroups.SourceGeneration
