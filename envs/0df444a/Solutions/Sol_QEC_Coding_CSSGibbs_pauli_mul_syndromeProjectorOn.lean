-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.pauli_mul_syndromeProjectorOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:22:27.774194+00:00
-- url     : https://prove2.me/submissions/89a566ac-33a3-4af2-9d1d-41b3f6984ffd

import Definitions.Def_QEC_Coding_CSS_Syndrome
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Projectors
import Theorems.Thm_QEC_Coding_CSSGibbs_pauli_mul_jointStabilizerFactor
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
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
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
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
attribute [local simp] QEC.Semantics.traceNorm_neg



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.CSSGibbs
open Classical PauliSymplectic StabilizerCode Semantics
open scoped BigOperators
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace QEC.Coding.CSSGibbs
theorem _root_.solution
    (checks : κ → Binary ι) (hcomm : ∀ a b, Commutes (checks a) (checks b))
    (error : Binary ι) (syndrome : JointSyndrome κ)
    (selected : Finset κ) :
    toHermitianQubitOperator error *
        selected.noncommProd (jointStabilizerFactor checks syndrome)
          (syndromeFactor_pairwise checks hcomm syndrome selected) =
      selected.noncommProd
          (jointStabilizerFactor checks
            (transportSyndrome checks hcomm error syndrome))
          (syndromeFactor_pairwise checks hcomm
            (transportSyndrome checks hcomm error syndrome) selected) *
        toHermitianQubitOperator error := by
  classical
  induction selected using Finset.induction_on with
  | empty => simp [Finset.noncommProd_empty]
  | @insert check selected hnotmem induction =>
      rw [Finset.noncommProd_insert_of_notMem selected check
        (jointStabilizerFactor checks syndrome)
        (syndromeFactor_pairwise checks hcomm syndrome (insert check selected)) hnotmem]
      rw [Finset.noncommProd_insert_of_notMem selected check
        (jointStabilizerFactor checks
          (transportSyndrome checks hcomm error syndrome))
        (syndromeFactor_pairwise checks hcomm
          (transportSyndrome checks hcomm error syndrome) (insert check selected)) hnotmem]
      calc
        toHermitianQubitOperator error *
            (jointStabilizerFactor checks syndrome check *
              selected.noncommProd (jointStabilizerFactor checks syndrome) _) =
            (toHermitianQubitOperator error *
                jointStabilizerFactor checks syndrome check) *
              selected.noncommProd (jointStabilizerFactor checks syndrome) _ := by
                rw [mul_assoc]
        _ = (jointStabilizerFactor checks
              (transportSyndrome checks hcomm error syndrome) check *
                toHermitianQubitOperator error) *
              selected.noncommProd (jointStabilizerFactor checks syndrome) _ := by
                rw [pauli_mul_jointStabilizerFactor checks hcomm error syndrome check]
        _ = jointStabilizerFactor checks
              (transportSyndrome checks hcomm error syndrome) check *
            (toHermitianQubitOperator error *
              selected.noncommProd (jointStabilizerFactor checks syndrome) _) := by
                rw [mul_assoc]
        _ = jointStabilizerFactor checks
              (transportSyndrome checks hcomm error syndrome) check *
            (selected.noncommProd
                (jointStabilizerFactor checks
                  (transportSyndrome checks hcomm error syndrome)) _ *
              toHermitianQubitOperator error) := by
                rw [induction]
        _ = (jointStabilizerFactor checks
              (transportSyndrome checks hcomm error syndrome) check *
                selected.noncommProd
                  (jointStabilizerFactor checks
                    (transportSyndrome checks hcomm error syndrome)) _) *
              toHermitianQubitOperator error := by
                rw [mul_assoc]
end QEC.Coding.CSSGibbs
