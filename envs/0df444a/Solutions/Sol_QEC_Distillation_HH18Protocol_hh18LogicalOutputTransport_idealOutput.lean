-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18LogicalOutputTransport_idealOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:00:11.388419+00:00
-- url     : https://prove2.me/submissions/9fb1fa82-1746-4afe-8822-4a3704def346

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_DecodedErrorBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18LogicalOutputTransport_idealOutputState
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
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
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open OneQubitMagic
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instOutputHandoffClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instOutputHandoffClassicalDecidable
namespace QEC.Distillation.HH18Protocol
theorem _root_.solution :
    hh18LogicalOutputTransport.conjDensity idealLogicalTOutput = aZeroDensity := by
  apply DensityOperator.ext_toOperator
  rw [UnitaryTransport.conjDensity_toOperator, idealLogicalTOutput,
    DensityOperator.pureDensity_toOperator, QuditSubsystem.conjOperator_rankOne,
    hh18LogicalOutputTransport_idealOutputState, aZeroDensity,
    OneQubitMagic.phaseStateDensity_toOperator]
  rfl
end QEC.Distillation.HH18Protocol
