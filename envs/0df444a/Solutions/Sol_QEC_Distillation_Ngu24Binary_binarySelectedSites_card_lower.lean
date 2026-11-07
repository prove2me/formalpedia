-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binarySelectedSites_card_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:14:03.00098+00:00
-- url     : https://prove2.me/submissions/8c168a02-b1c0-4214-92bd-4617f2369ab5

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTriples
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryPi2_symm_apply
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryPi3_symm_apply
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binarySelectedSites_card
import Theorems.Thm_QEC_Coding_f256SelectedCoordinates_card_ge_one
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
    Fintype.card J ≤ (binarySelectedSites J).card := by
  rw [binarySelectedSites_card]
  simpa using Nat.mul_le_mul_left (Fintype.card J) f256SelectedCoordinates_card_ge_one
end QEC.Distillation.Ngu24Binary
