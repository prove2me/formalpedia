-- Prove2me | solution 1 for QEC.Semantics.FiniteMatrixEntropy.partialTraceRightRaw_trace_pairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:53:18.855655+00:00
-- url     : https://prove2.me/submissions/0179abba-8513-4e08-b9db-970d7400b4d0

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_rightCompression_adjoint_sum
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Locality_partialTraceRightRaw_eq_rightCompression
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
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
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
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
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.logMatrix_apply
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.log2Matrix_apply

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder Kronecker TensorProduct
noncomputable section
open QEC.Semantics.FiniteMatrixEntropy
namespace QEC.Semantics.FiniteMatrixEntropy
theorem _root_.solution
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {beta : Type u} [Fintype beta]
    (b : OrthonormalBasis beta Complex K) (A : Operator (CompositeSystem H K))
    (X : Operator H) :
    LinearMap.trace Complex H (((partialTraceRightRaw H K) A).comp X) =
      LinearMap.trace Complex (CompositeSystem H K)
        (A.comp (TensorProduct.map X (LinearMap.id : K →ₗ[Complex] K))) := by
  let S : beta -> H →ₗ[Complex] CompositeSystem H K :=
    fun i => QEC.Locality.tensorRight H K (b i)
  let T : beta -> Operator H :=
    fun i => (LinearMap.adjoint (S i)).comp (A.comp (S i))
  have hright : QEC.Locality.rightCompression H K b A = ∑ i, T i := by
    apply LinearMap.ext
    intro z
    simp [QEC.Locality.rightCompression, S, T]
  rw [QEC.Locality.partialTraceRightRaw_eq_rightCompression H K b, hright]
  have hcompose : (∑ i, T i).comp X = ∑ i, (T i).comp X := by
    ext z
    simp [LinearMap.comp_apply]
  rw [hcompose, map_sum]
  calc
    _ = ∑ i, LinearMap.trace Complex (CompositeSystem H K)
        (A.comp ((S i).comp (X.comp (LinearMap.adjoint (S i))))) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa [T, LinearMap.comp_assoc] using
        (LinearMap.trace_comp_comm'
          (A.comp ((S i).comp X)) (LinearMap.adjoint (S i)))
    _ = LinearMap.trace Complex (CompositeSystem H K)
        (A.comp (∑ i, (S i).comp (X.comp (LinearMap.adjoint (S i))))) := by
      symm
      have hdistribute :
          A.comp (∑ i, (S i).comp (X.comp (LinearMap.adjoint (S i)))) =
            ∑ i, A.comp ((S i).comp (X.comp (LinearMap.adjoint (S i)))) := by
        ext z
        simp [LinearMap.comp_apply]
      rw [hdistribute, map_sum]
    _ = _ := by
      rw [rightCompression_adjoint_sum b X]
end QEC.Semantics.FiniteMatrixEntropy
