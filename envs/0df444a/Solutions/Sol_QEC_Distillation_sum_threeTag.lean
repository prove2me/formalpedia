-- Prove2me | solution 1 for QEC.Distillation.sum_threeTag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:46:50.261798+00:00
-- url     : https://prove2.me/submissions/1cff19db-163e-4f58-8ba6-f1a738e3d709

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
namespace QEC.Distillation
theorem _root_.solution {A R : Type} [Fintype A] [AddCommMonoid R]
    (f : (ThreeCopyTag → A) → R) :
    (∑ h, f h) = ∑ a, ∑ b, ∑ c, f (threeTagEquiv A (a, b, c)) := by
  rw [← Fintype.sum_equiv (threeTagEquiv A) (fun t => f (threeTagEquiv A t)) f (fun _ => rfl)]
  simp only [Fintype.sum_prod_type]
end QEC.Distillation
