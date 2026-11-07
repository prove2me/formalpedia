-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binarySelectedSites_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:12:04.215201+00:00
-- url     : https://prove2.me/submissions/891aa93c-63f5-4570-8f43-42f83989c0f9

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTriples
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryPi2_symm_apply
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryPi3_symm_apply
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


attribute [local simp] QEC.Distillation.Ngu24Binary.binaryPi2_symm_apply
attribute [local simp] QEC.Distillation.Ngu24Binary.binaryPi3_symm_apply

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding
open scoped BigOperators
universe u
variable (J : Type u)
variable [Fintype J]
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution :
    (binarySelectedSites J).card = Fintype.card J * f256SelectedCoordinates.card := by
  simp [binarySelectedSites]
end QEC.Distillation.Ngu24Binary
