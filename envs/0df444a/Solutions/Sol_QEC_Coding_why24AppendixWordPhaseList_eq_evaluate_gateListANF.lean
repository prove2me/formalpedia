-- Prove2me | solution 1 for QEC.Coding.why24AppendixWordPhaseList_eq_evaluate_gateListANF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:40:01.829412+00:00
-- url     : https://prove2.me/submissions/1b9d6a65-021c-40eb-aafa-0f44f68fe9b7

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Evaluation
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Certificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Data
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_Why24BooleanANF_evaluate_generator
import Theorems.Thm_QEC_Coding_Why24BooleanANF_generator_mul_self
import Theorems.Thm_QEC_Coding_why24QuditZ_apply
import Theorems.Thm_QEC_Coding_why24U_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
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
attribute [local simp] QEC.Coding.Why24BooleanANF.evaluate_generator
attribute [local simp] QEC.Coding.Why24BooleanANF.generator_mul_self
attribute [local simp] QEC.Coding.why24QuditZ_apply
attribute [local simp] QEC.Coding.why24U_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
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
open QEC QEC.Coding
open scoped BigOperators
open Why24BooleanANF
open Why24AppendixANF
namespace QEC.Coding
theorem _root_.solution
    (gates : List Why24AppendixGate) (word : Why24AppendixANF.Word) :
    why24AppendixWordPhaseList gates word =
      evaluate word (why24AppendixGateListANF gates) := by
  induction gates with
  | nil => simp [why24AppendixWordPhaseList, why24AppendixGateListANF]
  | cons gate gates ih =>
      simp only [why24AppendixWordPhaseList, why24AppendixGateListANF,
        List.foldr_cons, map_add] at ih ⊢
      rw [ih]
      cases gate with
      | z site =>
          simp [why24AppendixWordGatePhase, why24AppendixGateANF,
            evaluate_generator]
      | cz left right =>
          simp [why24AppendixWordGatePhase, why24AppendixGateANF,
            evaluate_generator]
      | ccz first second third =>
          simp [why24AppendixWordGatePhase, why24AppendixGateANF,
            evaluate_generator]
end QEC.Coding
