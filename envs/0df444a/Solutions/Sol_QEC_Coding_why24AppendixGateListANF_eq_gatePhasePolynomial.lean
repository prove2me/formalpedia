-- Prove2me | solution 1 for QEC.Coding.why24AppendixGateListANF_eq_gatePhasePolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:58:43.395895+00:00
-- url     : https://prove2.me/submissions/e99a1de1-3487-4f5a-a9de-f05ff85496f1

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Evaluation
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Certificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Data
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_Why24AppendixANF_cubicGateTriples_ANF_sum
import Theorems.Thm_QEC_Coding_Why24AppendixANF_fintype_sum_triple
import Theorems.Thm_QEC_Coding_Why24AppendixANF_quadraticGatePairs_ANF_sum
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


section
noncomputable section
namespace QEC.Coding
open scoped BigOperators
open Why24BooleanANF
open Why24AppendixANF
private theorem gateListANF_append (left right : List Why24AppendixGate) :
    why24AppendixGateListANF (left ++ right) =
      why24AppendixGateListANF left + why24AppendixGateListANF right := by
  induction left with
  | nil => simp [why24AppendixGateListANF]
  | cons gate gates ih =>
      change why24AppendixGateANF gate +
          why24AppendixGateListANF (gates ++ right) =
        (why24AppendixGateANF gate + why24AppendixGateListANF gates) +
          why24AppendixGateListANF right
      rw [ih, add_assoc]
private theorem gateListANF_eq_sum_map (gates : List Why24AppendixGate) :
    why24AppendixGateListANF gates =
      (gates.map why24AppendixGateANF).sum := by
  induction gates with
  | nil => rfl
  | cons gate gates ih =>
      change why24AppendixGateANF gate + why24AppendixGateListANF gates =
        why24AppendixGateANF gate +
          (gates.map why24AppendixGateANF).sum
      rw [ih]
private theorem zGateListANF_eq :
    why24AppendixGateListANF why24AppendixZGateList =
      ∑ site : Fin 10, generator site := by
  rw [gateListANF_eq_sum_map]
  simp only [why24AppendixZGateList, List.map_ofFn, why24AppendixGateANF,
    Function.comp_apply, Fin.sum_ofFn]
private theorem quadraticGateListANF_eq :
    why24AppendixGateListANF
        (quadraticGatePairs.map (fun pair => .cz pair.1 pair.2)) =
      ∑ left : Fin 10, ∑ right : Fin 10,
        if left < right then
          quadraticGateCoefficient left right •
            (generator left * generator right)
        else 0 := by
  rw [gateListANF_eq_sum_map]
  simp only [List.map_map]
  calc
    (quadraticGatePairs.map
        (fun pair => generator pair.1 * generator pair.2)).sum =
        ∑ pair : Fin 10 × Fin 10,
          if pair.1 < pair.2 then
            quadraticGateCoefficient pair.1 pair.2 •
              (generator pair.1 * generator pair.2)
          else 0 := quadraticGatePairs_ANF_sum
    _ = ∑ left : Fin 10, ∑ right : Fin 10,
        if left < right then
          quadraticGateCoefficient left right •
            (generator left * generator right)
        else 0 := by
      rw [Fintype.sum_prod_type]
private theorem cubicGateListANF_eq :
    why24AppendixGateListANF
        (cubicGateTriples.map
          (fun triple => .ccz triple.1 triple.2.1 triple.2.2)) =
      ∑ first : Fin 10, ∑ second : Fin 10, ∑ third : Fin 10,
        if first < second ∧ second < third then
          cubicGateCoefficient first second third •
            (generator first * generator second * generator third)
        else 0 := by
  rw [gateListANF_eq_sum_map]
  simp only [List.map_map]
  calc
    (cubicGateTriples.map
        (fun triple => generator triple.1 * generator triple.2.1 *
          generator triple.2.2)).sum =
        ∑ triple : Fin 10 × Fin 10 × Fin 10,
          if triple.1 < triple.2.1 ∧ triple.2.1 < triple.2.2 then
            cubicGateCoefficient triple.1 triple.2.1 triple.2.2 •
              (generator triple.1 * generator triple.2.1 *
                generator triple.2.2)
          else 0 := cubicGateTriples_ANF_sum
    _ = ∑ first : Fin 10, ∑ second : Fin 10, ∑ third : Fin 10,
        if first < second ∧ second < third then
          cubicGateCoefficient first second third •
            (generator first * generator second * generator third)
        else 0 := by
      exact fintype_sum_triple (fun first second third =>
        if first < second ∧ second < third then
          cubicGateCoefficient first second third •
            (generator first * generator second * generator third)
        else 0)
end QEC.Coding
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
open Why24BooleanANF
open Why24AppendixANF
namespace QEC.Coding
theorem _root_.solution :
    why24AppendixGateListANF why24AppendixGateList = gatePhasePolynomial := by
  rw [why24AppendixGateList, gateListANF_append, gateListANF_append,
    zGateListANF_eq, quadraticGateListANF_eq, cubicGateListANF_eq,
    gatePhasePolynomial]
end QEC.Coding
