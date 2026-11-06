-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensor_inducedMap_tensorMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:02:45.857139+00:00
-- url     : https://prove2.me/submissions/fabb3071-fee4-4750-a47b-7022fc357949

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProduct
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProductFunctorial
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerHistoryAt_map
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_fixedDensityReplacementSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerObservedAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_rawBranchOperator_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_rawBranchOperator_tensor_product
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_succ_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_zero_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitBitstringEquiv_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitRegisterTransport_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedPartialTraceChannel_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedRegisterReindex_apply_basis
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


attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerHistoryAt_map
section
universe u v w x y
namespace QEC
namespace Semantics
noncomputable section
namespace FiniteInstrument
open scoped BigOperators TensorProduct
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
  [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L]
  [FiniteQuantumSystem L]
private theorem tensorMap_sum_sum
    {kappa : Type v} {kappaTwo : Type x}
    [Fintype kappa] [Fintype kappaTwo]
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A]
    [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [FiniteQuantumSystem B]
    (left : kappa → Operator A) (right : kappaTwo → Operator B) :
    TensorProduct.map (∑ i, left i) (∑ j, right j) =
      ∑ i, ∑ j, TensorProduct.map (left i) (right j) := by
  classical
  have hleft (indices : Finset kappa) :
      TensorProduct.map (∑ i ∈ indices, left i) (∑ j, right j) =
        ∑ i ∈ indices, TensorProduct.map (left i) (∑ j, right j) := by
    induction indices using Finset.induction_on with
    | empty => simp
    | @insert index indices hindex ih =>
        simp [Finset.sum_insert hindex, TensorProduct.map_add_left, ih]
  have hright (i : kappa) (indices : Finset kappaTwo) :
      TensorProduct.map (left i) (∑ j ∈ indices, right j) =
        ∑ j ∈ indices, TensorProduct.map (left i) (right j) := by
    induction indices using Finset.induction_on with
    | empty => simp
    | @insert index indices hindex ih =>
        simp [Finset.sum_insert hindex, TensorProduct.map_add_right, ih]
  calc
    TensorProduct.map (∑ i, left i) (∑ j, right j) =
        ∑ i, TensorProduct.map (left i) (∑ j, right j) := by
          simpa using hleft Finset.univ
    _ = ∑ i, ∑ j, TensorProduct.map (left i) (right j) := by
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
noncomputable section
open QEC.Semantics.FiniteInstrument
open scoped BigOperators TensorProduct
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
  [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L]
  [FiniteQuantumSystem L]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    {kappa : Type v} {omega : Type w}
    {kappaTwo : Type x} {omegaTwo : Type y}
    [Fintype kappa] [Fintype kappaTwo] [Fintype omega] [Fintype omegaTwo]
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A]
    [FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D]
    [FiniteQuantumSystem D]
    (first : FiniteInstrument kappa omega A B)
    (second : FiniteInstrument kappaTwo omegaTwo C D)
    (left : Operator A) (right : Operator C) :
    (first.tensor second).kraus.inducedMap
        (TensorProduct.map left right) =
      TensorProduct.map (first.kraus.inducedMap left)
        (second.kraus.inducedMap right) := by
  rw [FiniteKrausFamily.inducedMap_apply,
    FiniteKrausFamily.inducedMap_apply,
    FiniteKrausFamily.inducedMap_apply]
  rw [Fintype.sum_prod_type, tensorMap_sum_sum]
  apply Finset.sum_congr rfl
  intro firstIndex _
  apply Finset.sum_congr rfl
  intro secondIndex _
  exact rawBranchOperator_tensor_product first second left right
    firstIndex secondIndex
end QEC.Semantics.FiniteInstrument
