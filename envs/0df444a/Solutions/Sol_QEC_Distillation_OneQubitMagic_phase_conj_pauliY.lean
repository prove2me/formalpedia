-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phase_conj_pauliY
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:03:01.542949+00:00
-- url     : https://prove2.me/submissions/493a9e77-22c8-4664-83f0-c370bdaa9a54

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
    phaseTransport.conjOperator pauliY = -pauliX := by
  ext psi b
  change phaseOperator (pauliY (phaseInverseOperator psi)) b = (-pauliX) psi b
  fin_cases b <;>
    simp [← mul_assoc, Complex.I_mul_I]
end QEC.Distillation.OneQubitMagic
