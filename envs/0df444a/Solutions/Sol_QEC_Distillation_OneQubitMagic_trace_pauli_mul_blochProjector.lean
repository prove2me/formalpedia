-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.trace_pauli_mul_blochProjector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:08:38.712386+00:00
-- url     : https://prove2.me/submissions/ac77a9ea-0798-4644-8093-dc0293479fb8

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_pauliX_pauliX_trace
import Theorems.Thm_QEC_Semantics_Qubit_pauliX_pauliY_trace
import Theorems.Thm_QEC_Semantics_Qubit_pauliX_pauliZ_trace
import Theorems.Thm_QEC_Semantics_Qubit_pauliX_trace
import Theorems.Thm_QEC_Semantics_Qubit_pauliY_pauliX_trace
import Theorems.Thm_QEC_Semantics_Qubit_pauliY_pauliY_trace
import Theorems.Thm_QEC_Semantics_Qubit_pauliY_pauliZ_trace
import Theorems.Thm_QEC_Semantics_Qubit_pauliY_trace
import Theorems.Thm_QEC_Semantics_Qubit_pauliZ_pauliX_trace
import Theorems.Thm_QEC_Semantics_Qubit_pauliZ_pauliY_trace
import Theorems.Thm_QEC_Semantics_Qubit_pauliZ_pauliZ_trace
import Theorems.Thm_QEC_Semantics_Qubit_pauliZ_trace
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution
    (r : PauliAxis -> Real) (i : PauliAxis) :
    LinearMap.trace Complex QubitSpace
      (pauliOperator i * blochProjector r) = r i := by
  fin_cases i <;>
    simp [pauliOperator, blochProjector, blochOperator, mul_add,
      pauliX_trace, pauliY_trace, pauliZ_trace,
      pauliX_pauliX_trace, pauliX_pauliY_trace, pauliX_pauliZ_trace,
      pauliY_pauliX_trace, pauliY_pauliY_trace, pauliY_pauliZ_trace,
      pauliZ_pauliX_trace, pauliZ_pauliY_trace, pauliZ_pauliZ_trace] <;>
    ring
end QEC.Distillation.OneQubitMagic
