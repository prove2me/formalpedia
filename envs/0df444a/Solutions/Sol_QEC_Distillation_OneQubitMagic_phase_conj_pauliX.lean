-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phase_conj_pauliX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:02:40.760846+00:00
-- url     : https://prove2.me/submissions/0d8a3653-01ab-4888-8943-1bc696147c55

import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open scoped BigOperators
noncomputable section
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution :
    phaseTransport.conjOperator pauliX = pauliY := by
  ext psi b
  change phaseOperator (pauliX (phaseInverseOperator psi)) b = pauliY psi b
  fin_cases b <;>
    simp
end QEC.Distillation.OneQubitMagic
