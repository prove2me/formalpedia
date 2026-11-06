-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.degreeFailureEvent_measure_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:53:54.124479+00:00
-- url     : https://prove2.me/submissions/78a5d05c-a6a4-4317-8d23-5d58afcc110c

import Definitions.Def_QEC_Coding_FiberBundle_Core
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.LinearAlgebra.Matrix.Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_check_degree_upper_window
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_check_degree_lower_window
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_variable_degree_upper_window
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_variable_degree_lower_window
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiberBundle_multipleRotation_val
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
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
attribute [local simp] QEC.Coding.FiberBundle.multipleRotation_val
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
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
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


attribute [local simp] QEC.Coding.FiberBundle.RandomBase.independentProduct_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.distribution_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
universe u
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (i : DegreeFailureIndex r) :
    (distribution r Delta hDelta).toMeasure.real
        (degreeFailureEvent r Delta i) ≤
      Real.exp (-(Delta : Real) / 40000) := by
  rcases i with ⟨a, upper⟩ | ⟨b, upper⟩
  · cases upper
    · calc
        _ ≤ (distribution r Delta hDelta).toMeasure.real
            {sample |
              (checkDegree sample a : Real) ≤ 99 * Delta / 100} := by
          refine measureReal_mono ?_ (by finiteness)
          intro sample hs
          simp only [degreeFailureEvent, Set.mem_setOf_eq] at hs ⊢
          have hlt : 100 * checkDegree sample a < 99 * Delta :=
            Nat.lt_of_not_ge hs
          have hltR :
              (100 : Real) * checkDegree sample a < 99 * Delta := by
            exact_mod_cast hlt
          linarith
        _ ≤ _ := check_degree_lower_window r Delta hr hDelta a
    · calc
        _ ≤ (distribution r Delta hDelta).toMeasure.real
            {sample |
              (101 * (Delta : Real) / 100) ≤ checkDegree sample a} := by
          refine measureReal_mono ?_ (by finiteness)
          intro sample hs
          simp only [degreeFailureEvent, Set.mem_setOf_eq] at hs ⊢
          have hlt : 101 * Delta < 100 * checkDegree sample a :=
            Nat.lt_of_not_ge hs
          have hltR :
              (101 : Real) * Delta < 100 * checkDegree sample a := by
            exact_mod_cast hlt
          linarith
        _ ≤ _ := check_degree_upper_window r Delta hr hDelta a
  · cases upper
    · calc
        _ ≤ (distribution r Delta hDelta).toMeasure.real
            {sample |
              (variableDegree sample b : Real) ≤ 74 * Delta / 100} := by
          refine measureReal_mono ?_ (by finiteness)
          intro sample hs
          simp only [degreeFailureEvent, Set.mem_setOf_eq] at hs ⊢
          have hlt : 100 * variableDegree sample b < 74 * Delta :=
            Nat.lt_of_not_ge hs
          have hltR :
              (100 : Real) * variableDegree sample b < 74 * Delta := by
            exact_mod_cast hlt
          linarith
        _ ≤ Real.exp (-(Delta : Real) / 32000) :=
          variable_degree_lower_window r Delta hr hDelta b
        _ ≤ _ := by
          apply Real.exp_le_exp_of_le
          have hDelta_nonneg : (0 : Real) ≤ Delta := by positivity
          nlinarith
    · calc
        _ ≤ (distribution r Delta hDelta).toMeasure.real
            {sample |
              (76 * (Delta : Real) / 100) ≤ variableDegree sample b} := by
          refine measureReal_mono ?_ (by finiteness)
          intro sample hs
          simp only [degreeFailureEvent, Set.mem_setOf_eq] at hs ⊢
          have hlt : 76 * Delta < 100 * variableDegree sample b :=
            Nat.lt_of_not_ge hs
          have hltR :
              (76 : Real) * Delta < 100 * variableDegree sample b := by
            exact_mod_cast hlt
          linarith
        _ ≤ Real.exp (-(Delta : Real) / 32000) :=
          variable_degree_upper_window r Delta hr hDelta b
        _ ≤ _ := by
          apply Real.exp_le_exp_of_le
          have hDelta_nonneg : (0 : Real) ≤ Delta := by positivity
          nlinarith
end QEC.Coding.FiberBundle.RandomBase
