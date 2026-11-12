-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18LogicalPlusInput_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:52:11.948418+00:00
-- url     : https://prove2.me/submissions/999455a9-5345-4c8e-89c7-c7b305ea6ca3

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalTypes
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_inner_self


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
universe u
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Protocol
theorem _root_.solution : ‖HH18NoisyInput.hh18LogicalPlusInput‖ = 1 := by
  have hinner := Triorthogonal.BinaryRowFamily.logicalPlusState_inner_self
    (HH18PuncturedReedMuller.LogicalSite 4 0)
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hsquare : ‖HH18NoisyInput.hh18LogicalPlusInput‖ ^ 2 = 1 := by
    change ‖Triorthogonal.BinaryRowFamily.logicalPlusState
      (HH18PuncturedReedMuller.LogicalSite 4 0)‖ ^ 2 = 1
    apply Complex.ofReal_injective
    rw [Complex.ofReal_pow]
    exact hinner
  nlinarith [norm_nonneg HH18NoisyInput.hh18LogicalPlusInput]
end QEC.Distillation.HH18Protocol
