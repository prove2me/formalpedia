-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phase_conj_pauliZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:03:04.723125+00:00
-- url     : https://prove2.me/submissions/75cf9565-1aa8-4160-9649-74e7ad81e4d2

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
    phaseTransport.conjOperator pauliZ = pauliZ := by
  ext psi b
  change phaseOperator (pauliZ (phaseInverseOperator psi)) b = pauliZ psi b
  fin_cases b <;>
    simp [← mul_assoc, Complex.I_mul_I]
end QEC.Distillation.OneQubitMagic
