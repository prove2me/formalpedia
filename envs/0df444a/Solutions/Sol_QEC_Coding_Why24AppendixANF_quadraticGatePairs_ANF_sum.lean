-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.quadraticGatePairs_ANF_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:41:22.324001+00:00
-- url     : https://prove2.me/submissions/bc3165d2-6167-47c6-802f-0e5e11bf64a4

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ListStructure
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Certificate
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_Why24AppendixANF_quadraticGateCoefficient_eq_indicator
import Theorems.Thm_QEC_Coding_Why24AppendixANF_quadraticGatePairs_nodup
import Theorems.Thm_QEC_Coding_Why24AppendixANF_quadraticGatePairs_ordered
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
namespace QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF
private theorem listSum_eq_fintypeIndicator
    {Entry Value : Type*} [Fintype Entry] [BEq Entry] [LawfulBEq Entry]
    [DecidableEq Entry]
    [AddCommMonoid Value] (entries : List Entry) (hentries : entries.Nodup)
    (value : Entry → Value) :
    (entries.map value).sum =
      ∑ entry : Entry, if entry ∈ entries then value entry else 0 := by
  classical
  calc
    (entries.map value).sum = ∑ entry ∈ entries.toFinset, value entry :=
      (List.sum_toFinset value hentries).symm
    _ = ∑ entry ∈ entries.toFinset,
        if entry ∈ entries then value entry else 0 := by
          apply Finset.sum_congr rfl
          intro entry hentry
          simp only [List.mem_toFinset.mp hentry, if_pos]
    _ = ∑ entry ∈ (Finset.univ : Finset Entry),
        if entry ∈ entries then value entry else 0 := by
          apply Finset.sum_subset (Finset.subset_univ entries.toFinset)
          intro entry _ hentry
          have hnot : entry ∉ entries := fun hmem =>
            hentry (List.mem_toFinset.mpr hmem)
          rw [if_neg hnot]
    _ = ∑ entry : Entry, if entry ∈ entries then value entry else 0 := rfl
private theorem listSum_eq_orderedCoefficient
    {Entry Value : Type*} [Fintype Entry] [BEq Entry] [LawfulBEq Entry]
    [DecidableEq Entry]
    [AddCommMonoid Value] [Module (ZMod 2) Value]
    (entries : List Entry) (hentries : entries.Nodup)
    (ordered : Entry → Prop) [DecidablePred ordered]
    (hordered : ∀ entry ∈ entries, ordered entry)
    (coefficient : Entry → ZMod 2)
    (hcoefficient : ∀ entry, coefficient entry =
      if entry ∈ entries then 1 else 0)
    (value : Entry → Value) :
    (entries.map value).sum =
      ∑ entry : Entry, if ordered entry then
        coefficient entry • value entry
      else 0 := by
  rw [listSum_eq_fintypeIndicator entries hentries]
  apply Finset.sum_congr rfl
  intro entry _
  by_cases hmem : entry ∈ entries
  · have hord := hordered entry hmem
    simp [hmem, hord, hcoefficient entry]
  · simp [hmem, hcoefficient entry]
end QEC.Coding.Why24AppendixANF
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution :
    (quadraticGatePairs.map
      (fun pair => generator pair.1 * generator pair.2)).sum =
      ∑ pair : Fin 10 × Fin 10, if pair.1 < pair.2 then
        quadraticGateCoefficient pair.1 pair.2 •
          (generator pair.1 * generator pair.2)
      else 0 := by
  exact listSum_eq_orderedCoefficient quadraticGatePairs
    quadraticGatePairs_nodup (fun pair => pair.1 < pair.2)
    quadraticGatePairs_ordered
    (fun pair => quadraticGateCoefficient pair.1 pair.2)
    quadraticGateCoefficient_eq_indicator
    (fun pair => generator pair.1 * generator pair.2)
end QEC.Coding.Why24AppendixANF
