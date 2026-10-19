-- Prove2me | solution 1 for SoficGroups.SourceGeneration.alphaBetaRoot_mem_sourceGenerated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/90785488-7b00-4c8a-b1b4-aaaaeab8470b

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceGeneration_alphaRoot_mem_sourceGenerated
import Theorems.Thm_SoficGroups_SourceGeneration_compressionU_mem_sourceGenerated
import Theorems.Thm_SoficGroups_SourceGeneration_compressionU_inv_mul_alphaWordS
import Theorems.Thm_SoficGroups_SourceGeneration_alphaWordT_mul_compressionU
import Theorems.Thm_SoficGroups_SourceGeneration_binaryBlockSandwich

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
      (alphaBetaNineIndex p i) (alphaBetaNineIndex q j)
      (alphaBetaNineIndex_ne hij p q) a ∈ sourceGeneratedGroup := by
  have hα := alphaRoot_mem_sourceGenerated i j hij
    (leavittS p * a * leavittT q)
  have hU := compressionU_mem_sourceGenerated
  have hconj :
      compressionU⁻¹ *
        prefixElementaryUnit alphaPrefixCode i j hij
          (leavittS p * a * leavittT q) * compressionU ∈
        sourceGeneratedGroup :=
    sourceGeneratedGroup.mul_mem
      (sourceGeneratedGroup.mul_mem (sourceGeneratedGroup.inv_mem hU) hα) hU
  have heq :
      compressionU⁻¹ *
        prefixElementaryUnit alphaPrefixCode i j hij
          (leavittS p * a * leavittT q) * compressionU =
        prefixElementaryUnit ninePrefixCode
          (alphaBetaNineIndex p i) (alphaBetaNineIndex q j)
          (alphaBetaNineIndex_ne hij p q) a := by
    apply Units.ext
    change
      (↑(compressionU⁻¹) : BinaryLeavitt) *
          (1 + leavittWordS (alphaWord i) *
            (leavittS p * a * leavittT q) *
            leavittWordT (alphaWord j)) *
          (compressionU : BinaryLeavitt) =
        1 + leavittWordS (nineWord (alphaBetaNineIndex p i)) * a *
          leavittWordT (nineWord (alphaBetaNineIndex q j))
    calc
      (↑(compressionU⁻¹) : BinaryLeavitt) *
          (1 + leavittWordS (alphaWord i) *
            (leavittS p * a * leavittT q) *
            leavittWordT (alphaWord j)) *
          (compressionU : BinaryLeavitt) =
        1 + ((↑(compressionU⁻¹) : BinaryLeavitt) *
            leavittWordS (alphaWord i)) *
          (leavittS p * a * leavittT q) *
          (leavittWordT (alphaWord j) * (compressionU : BinaryLeavitt)) := by
            simp [mul_add, add_mul, mul_assoc]
      _ = 1 +
          (leavittWordS (alphaWord i) * leavittT 0 +
            leavittWordS (betaWord i) * leavittT 1) *
          (leavittS p * a * leavittT q) *
          (leavittS 0 * leavittWordT (alphaWord j) +
            leavittS 1 * leavittWordT (betaWord j)) := by
              rw [compressionU_inv_mul_alphaWordS,
                alphaWordT_mul_compressionU]
      _ = 1 + leavittWordS (nineWord (alphaBetaNineIndex p i)) * a *
          leavittWordT (nineWord (alphaBetaNineIndex q j)) := by
            rw [binaryBlockSandwich]
            simp only [nineWord_alphaBetaNineIndex]
            split_ifs <;> rfl
  exact heq ▸ hconj
end SoficGroups.SourceGeneration
