-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.rotateTInvResource_clean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:13:56.937488+00:00
-- url     : https://prove2.me/submissions/980800e4-15b0-4c94-9500-8b411ef886a3

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalTypes
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Postselection
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourcePreparation
import Theorems.Thm_QEC_Distillation_HH18NoisyInput_tInvResourceErrorDensity_zero_eq_phaseStateDensity
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftOperator_phaseState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instClassicalDecidable
namespace QEC.Distillation.HH18Protocol
theorem _root_.solution :
    rotateTInvResource (HH18NoisyInput.tInvResourceErrorDensity 0) =
      Triorthogonal.BH12NoisyInjection.OneQubit.aZeroDensity := by
  apply DensityOperator.ext_toOperator
  rw [rotateTInvResource, UnitaryTransport.conjDensity_toOperator,
    HH18NoisyInput.tInvResourceErrorDensity_zero_eq_phaseStateDensity,
    OneQubitMagic.phaseStateDensity_toOperator,
    QuditSubsystem.conjOperator_rankOne,
    OneQubitMagic.phaseShiftTransport_apply,
    OneQubitMagic.phaseShiftOperator_phaseState,
    Triorthogonal.BH12NoisyInjection.OneQubit.aZeroDensity,
    OneQubitMagic.phaseStateDensity_toOperator]
  congr 1 <;> ring
end QEC.Distillation.HH18Protocol
