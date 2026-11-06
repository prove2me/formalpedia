-- Prove2me | solution 1 for QEC.Semantics.FiniteMatrixEntropy.trace_mul_logMatrix_eq_sum_overlap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:48:45.637294+00:00
-- url     : https://prove2.me/submissions/a2e7e896-ab30-4e64-bfb0-b9012bd635e6

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
set_option maxHeartbeats 3000000
namespace QEC.Semantics.FiniteMatrixEntropy
theorem _root_.solution {n : Type u} [Fintype n] [DecidableEq n]
    (A B : Matrix n n Complex) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * logMatrix B hB).trace =
      (∑ i, ∑ j,
        (hA.eigenvalues i * overlapWeight hA.eigenvectorUnitary hB.eigenvectorUnitary i j *
          Real.log (hB.eigenvalues j) : Real) : Complex) := by
  let U : Matrix.unitaryGroup n Complex := hA.eigenvectorUnitary
  let V : Matrix.unitaryGroup n Complex := hB.eigenvectorUnitary
  let W : Matrix.unitaryGroup n Complex := star U * V
  have hA_spectral :
      A = Unitary.conjStarAlgAut Complex _ U
        (Matrix.diagonal (Function.comp Complex.ofReal hA.eigenvalues)) := hA.spectral_theorem
  have hB_log :
      logMatrix B hB = Unitary.conjStarAlgAut Complex _ V
        (Matrix.diagonal
          (Function.comp Complex.ofReal (Function.comp Real.log hB.eigenvalues))) := by
    change hB.cfc Real.log = _
    rfl
  rw [hB_log]
  conv_lhs => arg 1; rw [hA_spectral]
  change
    Matrix.trace
      ((U : Matrix n n Complex) * Matrix.diagonal (Function.comp Complex.ofReal hA.eigenvalues) *
        star (U : Matrix n n Complex) *
        ((V : Matrix n n Complex) *
          Matrix.diagonal
            (Function.comp Complex.ofReal (Function.comp Real.log hB.eigenvalues)) *
          star (V : Matrix n n Complex))) = _
  calc
    _ = Matrix.trace
        ((U : Matrix n n Complex) *
          (Matrix.diagonal (Function.comp Complex.ofReal hA.eigenvalues) *
            (star (U : Matrix n n Complex) *
              ((V : Matrix n n Complex) *
                (Matrix.diagonal
                  (Function.comp Complex.ofReal (Function.comp Real.log hB.eigenvalues)) *
                  star (V : Matrix n n Complex)))))) := by
          congr 1
          noncomm_ring
    _ = Matrix.trace
        ((Matrix.diagonal (Function.comp Complex.ofReal hA.eigenvalues) *
          (star (U : Matrix n n Complex) *
            ((V : Matrix n n Complex) *
              (Matrix.diagonal
                (Function.comp Complex.ofReal (Function.comp Real.log hB.eigenvalues)) *
                star (V : Matrix n n Complex))))) * (U : Matrix n n Complex)) :=
          Matrix.trace_mul_comm _ _
    _ = Matrix.trace
        (Matrix.diagonal (Function.comp Complex.ofReal hA.eigenvalues) *
          ((W : Matrix n n Complex) *
            (Matrix.diagonal
              (Function.comp Complex.ofReal (Function.comp Real.log hB.eigenvalues)) *
              star (W : Matrix n n Complex))) ) := by
          congr 1
          simp [W, U, V, Matrix.mul_assoc]
    _ = _ := by
      simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Finset.mul_sum,
        overlapWeight, U, V, W, Complex.normSq_eq_conj_mul_self, mul_comm,
        mul_left_comm, mul_assoc]
      apply Finset.sum_congr rfl
      intro _ _
      rw [Finset.sum_comm]
end QEC.Semantics.FiniteMatrixEntropy
