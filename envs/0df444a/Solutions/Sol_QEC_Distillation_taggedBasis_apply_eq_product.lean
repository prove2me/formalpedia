-- Prove2me | solution 1 for QEC.Distillation.taggedBasis_apply_eq_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:46:51.75874+00:00
-- url     : https://prove2.me/submissions/87e13693-138d-42d9-935e-8ddf09b5599e

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Semantics_Core_ComputationalTensor
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_TensorRegister
import Theorems.Thm_QEC_Distillation_assembleTagged_extractBlock
import Theorems.Thm_QEC_Distillation_extractBlock_assembleTagged
import Theorems.Thm_QEC_Distillation_mem_coordinateSupport
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Distillation.assembleTagged_extractBlock
attribute [local simp] QEC.Distillation.extractBlock_assembleTagged
attribute [local simp] QEC.Distillation.mem_coordinateSupport
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
open Semantics
open scoped TensorProduct BigOperators
variable (F J K : Type) [Fintype F] [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]
namespace QEC.Distillation
theorem _root_.solution (u v : TaggedThreeCopyRegisterLabel F J) :
    EuclideanSpace.basisFun _ Complex u v =
      EuclideanSpace.basisFun (J → F) Complex (extractBlock u .first) (extractBlock v .first) *
        EuclideanSpace.basisFun (J → F) Complex (extractBlock u .second) (extractBlock v .second) *
        EuclideanSpace.basisFun (J → F) Complex (extractBlock u .third) (extractBlock v .third) := by
  classical
  have heq : v = u ↔ extractBlock v .first = extractBlock u .first ∧
      extractBlock v .second = extractBlock u .second ∧
      extractBlock v .third = extractBlock u .third := by
    constructor
    · rintro rfl
      exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨h₁, h₂, h₃⟩
      funext x
      rcases x with ⟨tag, j⟩
      cases tag with
      | first => exact congrFun h₁ j
      | second => exact congrFun h₂ j
      | third => exact congrFun h₃ j
  simp only [EuclideanSpace.basisFun_apply, PiLp.single_apply]
  simp only [heq]
  split_ifs <;> simp_all
end QEC.Distillation
