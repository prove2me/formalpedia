-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.stabilizerProjector_fixed_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:28:46.012073+00:00
-- url     : https://prove2.me/submissions/329d892c-057e-41ed-b7db-b4a2abfcf669

import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
open Semantics
open scoped BigOperators
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    (P : Binary ι) (outcome : StabilizerOutcome)
    (ψ : Qubit.QubitRegister ι) :
    stabilizerProjector P outcome ψ = ψ ↔
      toHermitianQubitOperator P ψ = outcome.sign • ψ := by
  cases outcome with
  | positive =>
      constructor
      · intro h
        have htwo := congrArg (fun x => (2 : Complex) • x) h
        simp [stabilizerProjector, StabilizerOutcome.sign, smul_add,
          smul_smul] at htwo
        have heigen : toHermitianQubitOperator P ψ = ψ :=
          add_left_cancel (a := ψ) (by simpa [two_smul] using htwo)
        simpa [StabilizerOutcome.sign] using heigen
      · intro h
        simp [stabilizerProjector, StabilizerOutcome.sign, h, smul_add]
        module
  | negative =>
      constructor
      · intro h
        have htwo := congrArg (fun x => (2 : Complex) • x) h
        simp [stabilizerProjector, StabilizerOutcome.sign, smul_add,
          smul_smul] at htwo
        have hnegative :
            -(toHermitianQubitOperator P ψ) = ψ :=
          add_left_cancel (a := ψ) (by simpa [two_smul] using htwo)
        have heigen : toHermitianQubitOperator P ψ = -ψ := by
          simpa only [neg_neg] using
            congrArg (fun x : Qubit.QubitRegister ι => -x) hnegative
        simpa [StabilizerOutcome.sign] using heigen
      · intro h
        simp [stabilizerProjector, StabilizerOutcome.sign, h, smul_add]
        module
end QEC.Coding.PauliSymplectic
