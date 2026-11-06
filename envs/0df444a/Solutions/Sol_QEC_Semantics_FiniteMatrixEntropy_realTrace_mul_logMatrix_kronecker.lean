-- Prove2me | solution 1 for QEC.Semantics.FiniteMatrixEntropy.realTrace_mul_logMatrix_kronecker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:14:54.311871+00:00
-- url     : https://prove2.me/submissions/03aa753a-1261-4013-a7bf-9699cb6bad44

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_realTrace_eq_sum_eigenvalues
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_trace_mul_logMatrix_eq_sum_eigenvalues
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_trace_mul_logMatrix_kronecker
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
theorem _root_.solution {m n : Type u}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m Complex) (B : Matrix n n Complex)
    (hA : A.PosDef) (hB : B.PosDef) :
    realTrace ((A ⊗ₖ B) *
        logMatrix (A ⊗ₖ B) (hA.kronecker hB).isHermitian) =
      realTrace (A * logMatrix A hA.isHermitian) * realTrace B +
        realTrace A * realTrace (B * logMatrix B hB.isHermitian) := by
  let hP : (A ⊗ₖ B).IsHermitian := (hA.kronecker hB).isHermitian
  have hproduct :
      realTrace ((A ⊗ₖ B) * logMatrix (A ⊗ₖ B) hP) =
        ∑ i, ∑ j,
          hA.isHermitian.eigenvalues i * hB.isHermitian.eigenvalues j *
            Real.log (hA.isHermitian.eigenvalues i * hB.isHermitian.eigenvalues j) := by
    unfold realTrace
    rw [trace_mul_logMatrix_kronecker A B hA hB]
    simp
  have hAlog : realTrace (A * logMatrix A hA.isHermitian) =
      ∑ i, hA.isHermitian.eigenvalues i * Real.log (hA.isHermitian.eigenvalues i) := by
    unfold realTrace
    rw [trace_mul_logMatrix_eq_sum_eigenvalues]
    simp
  have hBlog : realTrace (B * logMatrix B hB.isHermitian) =
      ∑ j, hB.isHermitian.eigenvalues j * Real.log (hB.isHermitian.eigenvalues j) := by
    unfold realTrace
    rw [trace_mul_logMatrix_eq_sum_eigenvalues]
    simp
  have hAtrace : realTrace A = ∑ i, hA.isHermitian.eigenvalues i :=
    realTrace_eq_sum_eigenvalues A hA.isHermitian
  have hBtrace : realTrace B = ∑ j, hB.isHermitian.eigenvalues j :=
    realTrace_eq_sum_eigenvalues B hB.isHermitian
  change realTrace ((A ⊗ₖ B) * logMatrix (A ⊗ₖ B) hP) = _
  rw [hproduct, hAlog, hBlog, hAtrace, hBtrace]
  calc
    _ = ∑ i, ∑ j,
        ((hA.isHermitian.eigenvalues i * Real.log (hA.isHermitian.eigenvalues i)) *
            hB.isHermitian.eigenvalues j +
          hA.isHermitian.eigenvalues i *
            (hB.isHermitian.eigenvalues j * Real.log (hB.isHermitian.eigenvalues j))) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Real.log_mul (hA.eigenvalues_pos i).ne' (hB.eigenvalues_pos j).ne']
      ring
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      apply congrArg₂ (fun x y : Real => x + y)
      · rw [Finset.sum_comm]
        calc
          _ = ∑ i, (∑ j, hA.isHermitian.eigenvalues j *
              Real.log (hA.isHermitian.eigenvalues j)) * hB.isHermitian.eigenvalues i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
          _ = _ := by rw [Finset.mul_sum]
      · rw [Finset.sum_comm]
        calc
          _ = ∑ i, (∑ j, hA.isHermitian.eigenvalues j) *
              (hB.isHermitian.eigenvalues i * Real.log (hB.isHermitian.eigenvalues i)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
          _ = _ := by rw [Finset.mul_sum]
end QEC.Semantics.FiniteMatrixEntropy
