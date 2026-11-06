-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.branchOperator_tensor_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:35:58.657193+00:00
-- url     : https://prove2.me/submissions/a760b620-94fd-44b1-9c3a-84af2da06204

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_rawBranchOperator_tensor_product
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


section
universe u v w x y
namespace QEC
namespace Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
namespace FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
section Tensor
variable {κ' : Type x} [Fintype κ']
variable {Ω' : Type y} [Fintype Ω']
variable {R S : Type u}
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]
private theorem tensorProduct_map_sum_sum
    (left : κ → Operator K) (right : κ' → Operator S) :
    TensorProduct.map (∑ i, left i) (∑ j, right j) =
      ∑ i, ∑ j, TensorProduct.map (left i) (right j) := by
  classical
  have hleft (indices : Finset κ) :
      TensorProduct.map (∑ i ∈ indices, left i) (∑ j, right j) =
        ∑ i ∈ indices, TensorProduct.map (left i) (∑ j, right j) := by
    induction indices using Finset.induction_on with
    | empty => simp
    | insert i indices hi ih =>
        simp [Finset.sum_insert hi, TensorProduct.map_add_left, ih]
  have hright (i : κ) (indices : Finset κ') :
      TensorProduct.map (left i) (∑ j ∈ indices, right j) =
        ∑ j ∈ indices, TensorProduct.map (left i) (right j) := by
    induction indices using Finset.induction_on with
    | empty => simp
    | insert j indices hj ih =>
        simp [Finset.sum_insert hj, TensorProduct.map_add_right, ih]
  calc
    TensorProduct.map (∑ i, left i) (∑ j, right j) =
        ∑ i, TensorProduct.map (left i) (∑ j, right j) := by
          simpa using hleft Finset.univ
    _ = ∑ i, ∑ j, TensorProduct.map (left i) (right j) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa using hright i Finset.univ
end Tensor
section DependentBind
variable {κ₂ : Ω → Type x} [∀ outcome, Fintype (κ₂ outcome)]
variable {L : Type u}
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
end DependentBind
section UnitFirstBind
variable {κ' : Type x} [Fintype κ']
variable {L : Type u}
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
end UnitFirstBind
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
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable {κ' : Type x} [Fintype κ']
variable {Ω' : Type y} [Fintype Ω']
variable {R S : Type u}
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    (I : FiniteInstrument κ Ω H K) (J : FiniteInstrument κ' Ω' R S)
    (A : Operator H) (B : Operator R)
    (leftOutcome : Ω) (rightOutcome : Ω') :
    (I.tensor J).branchOperator (leftOutcome, rightOutcome)
        (TensorProduct.map A B) =
      TensorProduct.map (I.branchOperator leftOutcome A)
        (J.branchOperator rightOutcome B) := by
  classical
  unfold branchOperator
  rw [Fintype.sum_prod_type, tensorProduct_map_sum_sum]
  apply Finset.sum_congr rfl
  intro leftIndex _
  apply Finset.sum_congr rfl
  intro rightIndex _
  by_cases hleft : I.observe leftIndex = leftOutcome
  · by_cases hright : J.observe rightIndex = rightOutcome
    · have hobserve :
          (I.tensor J).observe (leftIndex, rightIndex) =
            (leftOutcome, rightOutcome) := by
          exact Prod.ext hleft hright
      rw [if_pos hobserve, if_pos hleft, if_pos hright]
      simpa only [rawBranchOperator] using
        rawBranchOperator_tensor_product I J A B leftIndex rightIndex
    · have hobserve :
          (I.tensor J).observe (leftIndex, rightIndex) ≠
            (leftOutcome, rightOutcome) := by
          intro heq
          exact hright (congrArg Prod.snd heq)
      simp [hobserve, hleft, hright]
  · have hobserve :
        (I.tensor J).observe (leftIndex, rightIndex) ≠
          (leftOutcome, rightOutcome) := by
        intro heq
        exact hleft (congrArg Prod.fst heq)
    simp [hobserve, hleft]
end QEC.Semantics.FiniteInstrument
