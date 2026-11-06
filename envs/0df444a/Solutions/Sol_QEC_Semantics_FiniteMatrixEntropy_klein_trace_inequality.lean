-- Prove2me | solution 1 for QEC.Semantics.FiniteMatrixEntropy.klein_trace_inequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:55:28.060473+00:00
-- url     : https://prove2.me/submissions/bca6f5d1-3248-49d5-958f-264019f5917e

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_scalar_klein_log_weighted
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_overlapWeight_nonnegative
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_sum_overlapWeight_row_scale
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_sum_overlapWeight_column_scale
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_realTrace_eq_sum_eigenvalues
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_relativeEntropy_eq_sum_overlap
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
    (A B : Matrix n n Complex) (hA : A.PosSemidef) (hB : B.PosDef) :
    realTrace (A - B) <= relativeEntropy A B hA.isHermitian hB.isHermitian := by
  rw [relativeEntropy_eq_sum_overlap A B hA.isHermitian hB.isHermitian]
  calc
    realTrace (A - B) = realTrace A - realTrace B := by
      simp [realTrace]
    _ = (∑ i, hA.isHermitian.eigenvalues i) - (∑ j, hB.isHermitian.eigenvalues j) := by
      rw [realTrace_eq_sum_eigenvalues A hA.isHermitian,
        realTrace_eq_sum_eigenvalues B hB.isHermitian]
    _ = ∑ i, ∑ j,
        overlapWeight hA.isHermitian.eigenvectorUnitary hB.isHermitian.eigenvectorUnitary i j *
          (hA.isHermitian.eigenvalues i - hB.isHermitian.eigenvalues j) := by
      symm
      calc
        _ =
            (∑ i, ∑ j,
              overlapWeight hA.isHermitian.eigenvectorUnitary hB.isHermitian.eigenvectorUnitary i j *
                hA.isHermitian.eigenvalues i) -
              ∑ i, ∑ j,
                overlapWeight hA.isHermitian.eigenvectorUnitary hB.isHermitian.eigenvectorUnitary i j *
                  hB.isHermitian.eigenvalues j := by
                    simp_rw [mul_sub]
                    calc
                      _ = ∑ i,
                          ((∑ j,
                            overlapWeight hA.isHermitian.eigenvectorUnitary
                              hB.isHermitian.eigenvectorUnitary i j *
                              hA.isHermitian.eigenvalues i) -
                            ∑ j,
                              overlapWeight hA.isHermitian.eigenvectorUnitary
                                hB.isHermitian.eigenvectorUnitary i j *
                                hB.isHermitian.eigenvalues j) := by
                            apply Finset.sum_congr rfl
                            intro i _
                            rw [Finset.sum_sub_distrib]
                      _ = _ := by rw [Finset.sum_sub_distrib]
        _ = _ := by
          rw [sum_overlapWeight_row_scale hA.isHermitian.eigenvectorUnitary
            hB.isHermitian.eigenvectorUnitary hA.isHermitian.eigenvalues,
            sum_overlapWeight_column_scale hA.isHermitian.eigenvectorUnitary
              hB.isHermitian.eigenvectorUnitary hB.isHermitian.eigenvalues]
    _ <= ∑ i, ∑ j,
        overlapWeight hA.isHermitian.eigenvectorUnitary hB.isHermitian.eigenvectorUnitary i j *
          (hA.isHermitian.eigenvalues i *
            (Real.log (hA.isHermitian.eigenvalues i) -
              Real.log (hB.isHermitian.eigenvalues j))) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact scalar_klein_log_weighted (hA.eigenvalues_nonneg i) (hB.eigenvalues_pos j)
        (overlapWeight_nonnegative _ _ _ _)
end QEC.Semantics.FiniteMatrixEntropy
