-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.gatePhasePolynomial_apply_expanded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:35:16.744509+00:00
-- url     : https://prove2.me/submissions/4ed73cc3-bd9d-4cca-a619-4153f296c933

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Symbolic
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Target
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_Why24AppendixANF_generator_mul_generator
import Theorems.Thm_QEC_Coding_Why24AppendixANF_generator_mul_generator_mul_generator
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
private theorem singleSupport_smul_apply (support : Finset (Fin 10))
    (coefficient : ZMod 2) (monomial : Monomial 10) :
    (coefficient • MonoidAlgebra.single ⟨support⟩ 1 : ANF).coeff monomial =
      if support = monomial.support then coefficient else 0 := by
  have heq : (⟨support⟩ : Monomial 10) = monomial ↔
      support = monomial.support := by
    constructor
    · intro h
      exact congrArg Monomial.support h
    · intro h
      exact Monomial.ext h
  simp only [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single,
    Finsupp.single_apply, heq, smul_eq_mul]
  split_ifs <;> simp
private theorem generator_apply (coordinate : Fin 10) (monomial : Monomial 10) :
    (generator coordinate).coeff monomial =
      if {coordinate} = monomial.support then 1 else 0 := by
  rw [generator]
  simpa only [one_smul] using
    (singleSupport_smul_apply {coordinate} 1 monomial)
private theorem pairSummand_apply (left right : Fin 10)
    (monomial : Monomial 10) :
    (quadraticGateCoefficient left right •
        (generator left * generator right)).coeff monomial =
      if {left, right} = monomial.support then
        quadraticGateCoefficient left right
      else 0 := by
  rw [generator_mul_generator]
  exact singleSupport_smul_apply {left, right}
    (quadraticGateCoefficient left right) monomial
private theorem tripleSummand_apply (first second third : Fin 10)
    (monomial : Monomial 10) :
    (cubicGateCoefficient first second third •
        (generator first * generator second * generator third)).coeff monomial =
      if {first, second, third} = monomial.support then
        cubicGateCoefficient first second third
      else 0 := by
  rw [generator_mul_generator_mul_generator]
  exact singleSupport_smul_apply {first, second, third}
    (cubicGateCoefficient first second third) monomial
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
    gatePhasePolynomial.coeff monomial = expandedGateCoefficient monomial.support := by
  classical
  let coefficient : ANF →ₗ[ZMod 2] ZMod 2 :=
    (Finsupp.lapply monomial).comp (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).toLinearMap
  change coefficient gatePhasePolynomial = expandedGateCoefficient monomial.support
  have hlinear :
      coefficient (∑ coordinate : Fin 10, generator coordinate) =
        ∑ coordinate : Fin 10,
          if {coordinate} = monomial.support then 1 else 0 := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro coordinate _
    exact generator_apply coordinate monomial
  have hpair :
      coefficient
          (∑ left : Fin 10, ∑ right : Fin 10,
            if left < right then
              quadraticGateCoefficient left right •
                (generator left * generator right)
            else 0) =
        ∑ left : Fin 10, ∑ right : Fin 10,
          if left < right ∧ {left, right} = monomial.support then
            quadraticGateCoefficient left right
          else 0 := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro left _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro right _
    by_cases hlt : left < right
    · rw [if_pos hlt]
      change
        (quadraticGateCoefficient left right •
          (generator left * generator right)).coeff monomial = _
      rw [pairSummand_apply]
      simp only [hlt, true_and]
    · rw [if_neg hlt]
      simp [hlt]
  have htriple :
      coefficient
          (∑ first : Fin 10, ∑ second : Fin 10, ∑ third : Fin 10,
            if first < second ∧ second < third then
              cubicGateCoefficient first second third •
                (generator first * generator second * generator third)
            else 0) =
        ∑ first : Fin 10, ∑ second : Fin 10, ∑ third : Fin 10,
          if first < second ∧ second < third ∧
              {first, second, third} = monomial.support then
            cubicGateCoefficient first second third
          else 0 := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro first _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro second _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro third _
    by_cases hlt : first < second ∧ second < third
    · rw [if_pos hlt]
      change
        (cubicGateCoefficient first second third •
          (generator first * generator second * generator third)).coeff monomial = _
      rw [tripleSummand_apply]
      simp only [hlt.1, hlt.2, true_and]
    · rw [if_neg hlt]
      split_ifs with h
      · exact (hlt ⟨h.1, h.2.1⟩).elim
      · exact map_zero coefficient
  rw [gatePhasePolynomial, expandedGateCoefficient, map_add, map_add,
    hlinear, hpair, htriple]
end QEC.Coding.Why24AppendixANF
