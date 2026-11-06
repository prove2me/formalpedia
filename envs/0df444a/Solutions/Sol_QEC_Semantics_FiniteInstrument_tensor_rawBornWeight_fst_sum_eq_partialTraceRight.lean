-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensor_rawBornWeight_fst_sum_eq_partialTraceRight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:59:04.481359+00:00
-- url     : https://prove2.me/submissions/c1cbd840-e2b4-4830-bfb2-2ed6a29cd5cd

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalBornMass
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
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_partialTraceRightRaw_trace_pairing
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
private theorem tensorMap_sum_right
    (A : Operator H) (B : kappaTwo -> Operator R) :
    (∑ index, TensorProduct.map A (B index)) =
      TensorProduct.map A (∑ index, B index) := by
  classical
  induction (Finset.univ : Finset kappaTwo) using Finset.induction_on with
  | empty => simp
  | @insert index indices hindex ih =>
      simp [Finset.sum_insert hindex, TensorProduct.map_add_right, ih]
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
    (J : FiniteInstrument kappaTwo Xi R S) (hJ : J.kraus.Complete)
    (leftIndex : kappa) (rho : DensityOperator (CompositeSystem H R)) :
    (∑ rightIndex : kappaTwo,
      (I.tensor J).rawBornWeight (leftIndex, rightIndex) rho) =
      I.rawBornWeight leftIndex (partialTraceRightRaw_mapDensity H R rho) := by
  let leftEffect : Operator H :=
    (LinearMap.adjoint (I.kraus.operator leftIndex)).comp
      (I.kraus.operator leftIndex)
  let rightEffect : kappaTwo -> Operator R := fun rightIndex =>
    (LinearMap.adjoint (J.kraus.operator rightIndex)).comp
      (J.kraus.operator rightIndex)
  let basisR : OrthonormalBasis
      (ULift.{u} (Fin (Module.finrank Complex R))) Complex R :=
    (stdOrthonormalBasis Complex R).reindex Equiv.ulift.symm
  unfold rawBornWeight rawBranchOperator
  rw [← Complex.re_sum]
  apply congrArg Complex.re
  calc
    (∑ rightIndex : kappaTwo,
        LinearMap.trace Complex (CompositeSystem K S)
          (((I.tensor J).kraus.operator (leftIndex, rightIndex)).comp
            (rho.toOperator.comp
              (LinearMap.adjoint
                ((I.tensor J).kraus.operator (leftIndex, rightIndex)))))) =
        ∑ rightIndex : kappaTwo,
          LinearMap.trace Complex (CompositeSystem H R)
            (rho.toOperator.comp
              ((LinearMap.adjoint
                ((I.tensor J).kraus.operator (leftIndex, rightIndex))).comp
                ((I.tensor J).kraus.operator (leftIndex, rightIndex)))) := by
      apply Finset.sum_congr rfl
      intro rightIndex _
      simpa [LinearMap.comp_assoc] using
        (LinearMap.trace_comp_cycle
          (R := Complex) (M := CompositeSystem H R)
          (N := CompositeSystem H R) (P := CompositeSystem K S)
          (f := rho.toOperator)
          (g := (I.tensor J).kraus.operator (leftIndex, rightIndex))
          (h := LinearMap.adjoint
            ((I.tensor J).kraus.operator (leftIndex, rightIndex))))
    _ = ∑ rightIndex : kappaTwo,
        LinearMap.trace Complex (CompositeSystem H R)
          (rho.toOperator.comp
            (TensorProduct.map leftEffect (rightEffect rightIndex))) := by
      apply Finset.sum_congr rfl
      intro rightIndex _
      congr 2
      simp only [FiniteInstrument.tensor, TensorProduct.adjoint_map]
      rw [← TensorProduct.map_comp]
    _ = LinearMap.trace Complex (CompositeSystem H R)
        (rho.toOperator.comp
          (∑ rightIndex : kappaTwo,
            TensorProduct.map leftEffect (rightEffect rightIndex))) := by
      rw [← map_sum]
      congr 2
      ext vector
      simp [LinearMap.comp_apply]
    _ = LinearMap.trace Complex (CompositeSystem H R)
        (rho.toOperator.comp
          (TensorProduct.map leftEffect
            (∑ rightIndex : kappaTwo, rightEffect rightIndex))) := by
      rw [tensorMap_sum_right]
    _ = LinearMap.trace Complex (CompositeSystem H R)
        (rho.toOperator.comp
          (TensorProduct.map leftEffect (LinearMap.id : Operator R))) := by
      rw [show (∑ rightIndex : kappaTwo, rightEffect rightIndex) =
          (1 : Operator R) by exact hJ]
      rfl
    _ = LinearMap.trace Complex H
        (((partialTraceRightRaw H R) rho.toOperator).comp leftEffect) := by
      symm
      exact FiniteMatrixEntropy.partialTraceRightRaw_trace_pairing
        basisR rho.toOperator leftEffect
    _ = LinearMap.trace Complex K
        ((I.kraus.operator leftIndex).comp
          (((partialTraceRightRaw H R) rho.toOperator).comp
            (LinearMap.adjoint (I.kraus.operator leftIndex)))) := by
      simpa [leftEffect, LinearMap.comp_assoc] using
        (LinearMap.trace_comp_cycle
          (R := Complex) (M := H) (N := H) (P := K)
          (f := (partialTraceRightRaw H R) rho.toOperator)
          (g := I.kraus.operator leftIndex)
          (h := LinearMap.adjoint (I.kraus.operator leftIndex))).symm
end QEC.Semantics.FiniteInstrument
