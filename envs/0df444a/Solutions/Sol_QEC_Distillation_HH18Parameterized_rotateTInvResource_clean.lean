-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.rotateTInvResource_clean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:20:57.981389+00:00
-- url     : https://prove2.me/submissions/f1c1942e-4f16-49e7-95a2-5678788b69c6

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Preparation
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_ResourceMeasurement
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
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
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
  congr 1; ring_nf
end QEC.Distillation.HH18Parameterized
