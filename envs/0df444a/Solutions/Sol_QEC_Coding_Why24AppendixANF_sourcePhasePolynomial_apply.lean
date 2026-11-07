-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourcePhasePolynomial_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:35:12.398339+00:00
-- url     : https://prove2.me/submissions/1493814a-36ef-4742-ae57-421bbdf345ff

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Certificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Certificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Symbolic
import Theorems.Thm_QEC_Coding_Why24AppendixANF_generator_mul_generator_mul_generator
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


section
noncomputable section
namespace QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF
private theorem sourcePhaseSummand_apply
    (first second third : Fin 10) (monomial : Monomial 10) :
    (traceTensor first second third •
        (generator first * generator second * generator third)).coeff monomial =
      if tripleSupport first second third = monomial.support then
        traceTensor first second third
      else 0 := by
  have heq :
      (⟨{first, second, third}⟩ : Monomial 10) = monomial ↔
        tripleSupport first second third = monomial.support := by
    constructor
    · intro h
      simpa only [tripleSupport] using congrArg Monomial.support h
    · intro h
      apply Monomial.ext
      simpa only [tripleSupport] using h
  rw [generator_mul_generator_mul_generator]
  simp only [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single,
    Finsupp.single_apply, heq, smul_eq_mul]
  split_ifs <;> simp
end QEC.Coding.Why24AppendixANF
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (monomial : Monomial 10) :
    sourcePhasePolynomial.coeff monomial = sourceCoefficient monomial.support := by
  classical
  let coefficient : ANF →ₗ[ZMod 2] ZMod 2 :=
    (Finsupp.lapply monomial).comp (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).toLinearMap
  change coefficient sourcePhasePolynomial = sourceCoefficient monomial.support
  rw [sourcePhasePolynomial, sourceCoefficient, map_sum]
  apply Finset.sum_congr rfl
  intro first _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro second _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro third _
  change
    (traceTensor first second third •
      (generator first * generator second * generator third)).coeff monomial = _
  exact sourcePhaseSummand_apply first second third monomial
end QEC.Coding.Why24AppendixANF
