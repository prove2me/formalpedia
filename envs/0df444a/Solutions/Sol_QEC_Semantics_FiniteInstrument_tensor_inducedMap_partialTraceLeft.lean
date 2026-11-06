-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensor_inducedMap_partialTraceLeft
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:57:13.906034+00:00
-- url     : https://prove2.me/submissions/549b84ee-7f23-4c40-abc1-c9afb8e537d0

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalBornMass
import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_fixedDensityReplacementSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerObservedAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_rawBranchOperator_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_succ_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_zero_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitBitstringEquiv_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitRegisterTransport_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedPartialTraceChannel_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedRegisterReindex_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_partialTraceLeftRaw_trace_pairing
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_operator_ext_of_trace_comp_right_eq
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.fixedDensityReplacementSwap_apply_tmul
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerAcceptedIndices
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerObservedAcceptedIndices
attribute [local simp] QEC.Semantics.FiniteInstrument.rawBranchOperator_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerBasis_succ_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerBasis_zero_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitBitstringEquiv_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitRegisterTransport_apply_basis
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedRegisterReindex_apply_basis
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.log2Matrix_apply
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.logMatrix_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


section
universe u v w x y
namespace QEC
namespace Semantics
open Classical
open scoped BigOperators TensorProduct
noncomputable section
namespace FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {kappaTwo : Type x} [Fintype kappaTwo]
variable {Xi : Type y} [Fintype Xi]
variable {H K R S : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]
private theorem tensorMap_sum_sum
    (a : kappa -> Operator H) (b : kappaTwo -> Operator R) :
    TensorProduct.map (∑ i, a i) (∑ j, b j) =
      ∑ i, ∑ j, TensorProduct.map (a i) (b j) := by
  classical
  have hleft (indices : Finset kappa) :
      TensorProduct.map (∑ i ∈ indices, a i) (∑ j, b j) =
        ∑ i ∈ indices, TensorProduct.map (a i) (∑ j, b j) := by
    induction indices using Finset.induction_on with
    | empty => simp
    | @insert index indices hindex ih =>
        simp [Finset.sum_insert hindex, TensorProduct.map_add_left, ih]
  have hright (i : kappa) (indices : Finset kappaTwo) :
      TensorProduct.map (a i) (∑ j ∈ indices, b j) =
        ∑ j ∈ indices, TensorProduct.map (a i) (b j) := by
    induction indices using Finset.induction_on with
    | empty => simp
    | @insert index indices hindex ih =>
        simp [Finset.sum_insert hindex, TensorProduct.map_add_right, ih]
  calc
    TensorProduct.map (∑ i, a i) (∑ j, b j) =
        ∑ i, TensorProduct.map (a i) (∑ j, b j) := by
      simpa using hleft Finset.univ
    _ = ∑ i, ∑ j, TensorProduct.map (a i) (b j) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa using hright i Finset.univ
end FiniteInstrument
end
end Semantics
end QEC
end

set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {kappaTwo : Type x} [Fintype kappaTwo]
variable {Xi : Type y} [Fintype Xi]
variable {H K R S : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    (I : FiniteInstrument kappa Omega H K)
    (J : FiniteInstrument kappaTwo Xi R S) (hI : I.kraus.Complete)
    (A : Operator (CompositeSystem H R)) :
    FiniteMatrixEntropy.partialTraceLeftRaw K S
        ((I.tensor J).kraus.inducedMap A) =
      J.kraus.inducedMap
        (FiniteMatrixEntropy.partialTraceLeftRaw H R A) := by
  let leftEffect : kappa -> Operator H := fun leftIndex =>
    (LinearMap.adjoint (I.kraus.operator leftIndex)).comp
      (I.kraus.operator leftIndex)
  let rightEffect : kappaTwo -> Operator R := fun rightIndex =>
    (LinearMap.adjoint (J.kraus.operator rightIndex)).comp
      ((LinearMap.id : Operator S).comp (J.kraus.operator rightIndex))
  apply operator_ext_of_trace_comp_right_eq
  intro Y
  let testedRightEffect : kappaTwo -> Operator R := fun rightIndex =>
    (LinearMap.adjoint (J.kraus.operator rightIndex)).comp
      (Y.comp (J.kraus.operator rightIndex))
  calc
    LinearMap.trace Complex S
        (Y.comp (FiniteMatrixEntropy.partialTraceLeftRaw K S
          ((I.tensor J).kraus.inducedMap A))) =
      LinearMap.trace Complex S
        ((FiniteMatrixEntropy.partialTraceLeftRaw K S
          ((I.tensor J).kraus.inducedMap A)).comp Y) :=
      (LinearMap.trace_comp_comm' Y _).symm
    _ = LinearMap.trace Complex (CompositeSystem K S)
        (((I.tensor J).kraus.inducedMap A).comp
          (TensorProduct.map (LinearMap.id : Operator K) Y)) :=
      FiniteMatrixEntropy.partialTraceLeftRaw_trace_pairing
        ((I.tensor J).kraus.inducedMap A) Y
    _ = ∑ leftIndex : kappa, ∑ rightIndex : kappaTwo,
        LinearMap.trace Complex (CompositeSystem H R)
          (A.comp (TensorProduct.map
            (leftEffect leftIndex) (testedRightEffect rightIndex))) := by
      rw [FiniteKrausFamily.inducedMap_apply, Fintype.sum_prod_type]
      have hcomp :
          ((∑ leftIndex : kappa, ∑ rightIndex : kappaTwo,
              ((I.tensor J).kraus.operator (leftIndex, rightIndex)).comp
                (A.comp (LinearMap.adjoint
                  ((I.tensor J).kraus.operator (leftIndex, rightIndex))))) ).comp
              (TensorProduct.map (LinearMap.id : Operator K) Y) =
            ∑ leftIndex : kappa, ∑ rightIndex : kappaTwo,
              (((I.tensor J).kraus.operator (leftIndex, rightIndex)).comp
                (A.comp (LinearMap.adjoint
                  ((I.tensor J).kraus.operator (leftIndex, rightIndex))))).comp
                (TensorProduct.map (LinearMap.id : Operator K) Y) := by
        ext vector
        simp [LinearMap.comp_apply]
      rw [hcomp, map_sum]
      apply Finset.sum_congr rfl
      intro leftIndex _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro rightIndex _
      let localOperator :=
        TensorProduct.map (I.kraus.operator leftIndex)
          (J.kraus.operator rightIndex)
      have hcycle := LinearMap.trace_comp_cycle
        (R := Complex) (M := CompositeSystem H R)
        (N := CompositeSystem H R) (P := CompositeSystem K S)
        (f := A) (g := localOperator)
        (h := (LinearMap.adjoint localOperator).comp
          (TensorProduct.map (LinearMap.id : Operator K) Y))
      calc
        LinearMap.trace Complex (CompositeSystem K S)
            ((localOperator.comp
              (A.comp (LinearMap.adjoint localOperator))).comp
                (TensorProduct.map (LinearMap.id : Operator K) Y)) =
          LinearMap.trace Complex (CompositeSystem H R)
            (A.comp (((LinearMap.adjoint localOperator).comp
              (TensorProduct.map (LinearMap.id : Operator K) Y)).comp
                localOperator)) := by
          simpa [LinearMap.comp_assoc] using hcycle
        _ = _ := by
          congr 2
          simp only [localOperator, TensorProduct.adjoint_map]
          rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
          rfl
    _ = LinearMap.trace Complex (CompositeSystem H R)
        (A.comp (TensorProduct.map (∑ leftIndex, leftEffect leftIndex)
          (∑ rightIndex, testedRightEffect rightIndex))) := by
      rw [tensorMap_sum_sum]
      have hcomp :
          A.comp (∑ leftIndex : kappa, ∑ rightIndex : kappaTwo,
              TensorProduct.map (leftEffect leftIndex)
                (testedRightEffect rightIndex)) =
            ∑ leftIndex : kappa, ∑ rightIndex : kappaTwo,
              A.comp (TensorProduct.map (leftEffect leftIndex)
                (testedRightEffect rightIndex)) := by
        ext vector
        simp [LinearMap.comp_apply]
      rw [hcomp, map_sum]
      apply Finset.sum_congr rfl
      intro leftIndex _
      rw [map_sum]
    _ = LinearMap.trace Complex (CompositeSystem H R)
        (A.comp (TensorProduct.map (LinearMap.id : Operator H)
          (∑ rightIndex, testedRightEffect rightIndex))) := by
      rw [show (∑ leftIndex, leftEffect leftIndex) = (1 : Operator H) by
        exact hI]
      rfl
    _ = LinearMap.trace Complex R
        ((FiniteMatrixEntropy.partialTraceLeftRaw H R A).comp
          (∑ rightIndex, testedRightEffect rightIndex)) := by
      symm
      exact FiniteMatrixEntropy.partialTraceLeftRaw_trace_pairing
        A (∑ rightIndex, testedRightEffect rightIndex)
    _ = LinearMap.trace Complex S
        ((J.kraus.inducedMap
          (FiniteMatrixEntropy.partialTraceLeftRaw H R A)).comp Y) := by
      rw [FiniteKrausFamily.inducedMap_apply]
      have hcomp :
          (∑ rightIndex : kappaTwo,
              (J.kraus.operator rightIndex).comp
                ((FiniteMatrixEntropy.partialTraceLeftRaw H R A).comp
                  (LinearMap.adjoint (J.kraus.operator rightIndex)))).comp Y =
            ∑ rightIndex : kappaTwo,
              ((J.kraus.operator rightIndex).comp
                ((FiniteMatrixEntropy.partialTraceLeftRaw H R A).comp
                  (LinearMap.adjoint (J.kraus.operator rightIndex)))).comp Y := by
        ext vector
        simp [LinearMap.comp_apply]
      rw [hcomp, map_sum]
      have hdistribute :
          (FiniteMatrixEntropy.partialTraceLeftRaw H R A).comp
              (∑ rightIndex, testedRightEffect rightIndex) =
            ∑ rightIndex,
              (FiniteMatrixEntropy.partialTraceLeftRaw H R A).comp
                (testedRightEffect rightIndex) := by
        ext vector
        simp [LinearMap.comp_apply]
      rw [hdistribute, map_sum]
      apply Finset.sum_congr rfl
      intro rightIndex _
      simpa [testedRightEffect, LinearMap.comp_assoc] using
        (LinearMap.trace_comp_cycle
          (R := Complex) (M := R) (N := R) (P := S)
          (f := FiniteMatrixEntropy.partialTraceLeftRaw H R A)
          (g := J.kraus.operator rightIndex)
          (h := (LinearMap.adjoint (J.kraus.operator rightIndex)).comp Y)).symm
    _ = LinearMap.trace Complex S
        (Y.comp (J.kraus.inducedMap
          (FiniteMatrixEntropy.partialTraceLeftRaw H R A))) :=
      LinearMap.trace_comp_comm' _ _
end QEC.Semantics.FiniteInstrument
