-- Prove2me | solution 1 for QEC.Semantics.FiniteMatrixEntropy.trace_mul_cfc_eq_sum_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:41:07.503189+00:00
-- url     : https://prove2.me/submissions/95431e54-c097-4790-9ba8-10f27e6b1a32

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
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
theorem _root_.solution {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.IsHermitian) (f : Real -> Real) :
    (A * hA.cfc f).trace =
      (∑ i, (hA.eigenvalues i * f (hA.eigenvalues i) : Real) : Complex) := by
  rw [Matrix.IsHermitian.cfc]
  conv_lhs => arg 1; arg 1; rw [hA.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply]
  calc
    _ = Matrix.trace
        ((hA.eigenvectorUnitary : Matrix n n Complex) *
          (Matrix.diagonal (Function.comp (RCLike.ofReal : Real -> Complex) hA.eigenvalues) *
            ((star (hA.eigenvectorUnitary : Matrix n n Complex) *
              (hA.eigenvectorUnitary : Matrix n n Complex)) *
              (Matrix.diagonal
                (Function.comp (RCLike.ofReal : Real -> Complex)
                  (Function.comp f hA.eigenvalues)) *
                star (hA.eigenvectorUnitary : Matrix n n Complex))))) := by
          congr 1
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace
        ((hA.eigenvectorUnitary : Matrix n n Complex) *
          (Matrix.diagonal (Function.comp (RCLike.ofReal : Real -> Complex) hA.eigenvalues) *
            (Matrix.diagonal
              (Function.comp (RCLike.ofReal : Real -> Complex)
                (Function.comp f hA.eigenvalues)) *
              star (hA.eigenvectorUnitary : Matrix n n Complex)))) := by
          rw [Unitary.coe_star_mul_self]
          simp
    _ = Matrix.trace
        ((Matrix.diagonal (Function.comp (RCLike.ofReal : Real -> Complex) hA.eigenvalues) *
          (Matrix.diagonal
            (Function.comp (RCLike.ofReal : Real -> Complex)
              (Function.comp f hA.eigenvalues)) *
            star (hA.eigenvectorUnitary : Matrix n n Complex))) *
          (hA.eigenvectorUnitary : Matrix n n Complex)) :=
          Matrix.trace_mul_comm _ _
    _ = _ := by
      simp only [Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.mul_one]
      simp
end QEC.Semantics.FiniteMatrixEntropy
