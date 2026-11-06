-- Prove2me | solution 1 for QEC.Semantics.FiniteMatrixEntropy.trace_mul_logMatrix_kronecker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:51:44.188181+00:00
-- url     : https://prove2.me/submissions/58756271-b801-4977-add3-7f04d2c51b60

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_trace_mul_cfc_diagonal
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
set_option maxHeartbeats 1000000
namespace QEC.Semantics.FiniteMatrixEntropy
theorem _root_.solution {m n : Type u}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m Complex) (B : Matrix n n Complex)
    (hA : A.PosDef) (hB : B.PosDef) :
    ((A ⊗ₖ B) *
        logMatrix (A ⊗ₖ B) (hA.kronecker hB).isHermitian).trace =
      (∑ i, ∑ j,
        (hA.isHermitian.eigenvalues i * hB.isHermitian.eigenvalues j *
          Real.log (hA.isHermitian.eigenvalues i * hB.isHermitian.eigenvalues j) : Real) : Complex) := by
  let U : unitary (Matrix (m × n) (m × n) Complex) :=
    ⟨(hA.isHermitian.eigenvectorUnitary : Matrix m m Complex) ⊗ₖ
        (hB.isHermitian.eigenvectorUnitary : Matrix n n Complex),
      Matrix.kronecker_mem_unitary hA.isHermitian.eigenvectorUnitary.property
        hB.isHermitian.eigenvectorUnitary.property⟩
  let D : Matrix (m × n) (m × n) Complex :=
    Matrix.diagonal fun ij : m × n =>
      ((hA.isHermitian.eigenvalues ij.1 * hB.isHermitian.eigenvalues ij.2 : Real) : Complex)
  let hP : (A ⊗ₖ B).IsHermitian := (hA.kronecker hB).isHermitian
  have hD : D.IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro ij
    exact (Complex.im_eq_zero_iff_isSelfAdjoint _).mp (by simp)
  have hfactor : A ⊗ₖ B =
      (U : Matrix (m × n) (m × n) Complex) * D *
        star (U : Matrix (m × n) (m × n) Complex) := by
    rw [hA.isHermitian.spectral_theorem, hB.isHermitian.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply]
    have hstar : star
        ((hA.isHermitian.eigenvectorUnitary : Matrix m m Complex) ⊗ₖ
          (hB.isHermitian.eigenvectorUnitary : Matrix n n Complex)) =
        star (hA.isHermitian.eigenvectorUnitary : Matrix m m Complex) ⊗ₖ
          star (hB.isHermitian.eigenvectorUnitary : Matrix n n Complex) := by
      simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]
    rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]
    change
      ((hA.isHermitian.eigenvectorUnitary : Matrix m m Complex) ⊗ₖ
          (hB.isHermitian.eigenvectorUnitary : Matrix n n Complex)) *
          (Matrix.diagonal (Complex.ofReal ∘ hA.isHermitian.eigenvalues) ⊗ₖ
            Matrix.diagonal (Complex.ofReal ∘ hB.isHermitian.eigenvalues)) *
          (star (hA.isHermitian.eigenvectorUnitary : Matrix m m Complex) ⊗ₖ
            star (hB.isHermitian.eigenvectorUnitary : Matrix n n Complex)) =
        ((hA.isHermitian.eigenvectorUnitary : Matrix m m Complex) ⊗ₖ
          (hB.isHermitian.eigenvectorUnitary : Matrix n n Complex)) *
          Matrix.diagonal (fun ij =>
            ((hA.isHermitian.eigenvalues ij.1 * hB.isHermitian.eigenvalues ij.2 : Real) : Complex)) *
          star ((hA.isHermitian.eigenvectorUnitary : Matrix m m Complex) ⊗ₖ
            (hB.isHermitian.eigenvectorUnitary : Matrix n n Complex))
    rw [Matrix.diagonal_kronecker_diagonal, hstar]
    simp [Complex.ofReal_mul]
  let phi : Matrix (m × n) (m × n) Complex ≃⋆ₐ[Complex]
      Matrix (m × n) (m × n) Complex :=
    Unitary.conjStarAlgAut Complex _ U
  have hDpos : D.PosDef := by
    change (Matrix.diagonal fun ij : m × n =>
      ((hA.isHermitian.eigenvalues ij.1 * hB.isHermitian.eigenvalues ij.2 : Real) : Complex)).PosDef
    apply Matrix.posDef_diagonal_iff.mpr
    intro ij
    exact_mod_cast mul_pos (hA.eigenvalues_pos ij.1) (hB.eigenvalues_pos ij.2)
  have hlog_cont : ContinuousOn Real.log (spectrum Real D) :=
    Real.continuousOn_log.mono (by
      simpa only [Set.subset_compl_singleton_iff] using
        spectrum.zero_notMem Real hDpos.isUnit)
  have hphi_cont : Continuous phi := by
    change Continuous fun X : Matrix (m × n) (m × n) Complex =>
      (U : Matrix (m × n) (m × n) Complex) * X * star (U : Matrix (m × n) (m × n) Complex)
    fun_prop
  have hphiD : phi D = A ⊗ₖ B := by
    simpa [phi, Unitary.conjStarAlgAut_apply] using hfactor.symm
  have hphiHermitian : (phi D).IsHermitian := by
    rw [hphiD]
    exact hP
  have hmap : phi (cfc Real.log D) = cfc Real.log (phi D) :=
    StarAlgHomClass.map_cfc phi Real.log D hlog_cont hphi_cont hD hphiHermitian
  have hlog : logMatrix (A ⊗ₖ B) hP =
      (U : Matrix (m × n) (m × n) Complex) * cfc Real.log D *
        star (U : Matrix (m × n) (m × n) Complex) := by
    rw [logMatrix_apply, ← hP.cfc_eq]
    calc
      cfc Real.log (A ⊗ₖ B) = cfc Real.log (phi D) := by rw [hphiD]
      _ = phi (cfc Real.log D) := hmap.symm
      _ = _ := rfl
  change ((A ⊗ₖ B) * logMatrix (A ⊗ₖ B) hP).trace = _
  rw [hlog, hfactor]
  have hUleft : (star U : Matrix (m × n) (m × n) Complex) *
      (U : Matrix (m × n) (m × n) Complex) = 1 :=
    Matrix.UnitaryGroup.star_mul_self U
  have hUleft' :
      ((↑(star U) : Matrix (m × n) (m × n) Complex) *
        (↑U : Matrix (m × n) (m × n) Complex)) = (1 : Matrix (m × n) (m × n) Complex) := by
    simpa only [Unitary.coe_star] using hUleft
  calc
    _ = (U * (D * cfc Real.log D) * star U).trace := by
      congr 1
      calc
        U * D * star U * (U * cfc Real.log D * star U) =
            U * (D * ((star U * U) * cfc Real.log D)) * star U := by noncomm_ring
        _ = U * (D * cfc Real.log D) * star U := by
          rw [hUleft']
          simp [Matrix.mul_assoc]
    _ = (star U * (U * (D * cfc Real.log D))).trace :=
      Matrix.trace_mul_comm _ _
    _ = (D * cfc Real.log D).trace := by
      congr 1
      rw [← Matrix.mul_assoc, hUleft', Matrix.one_mul]
    _ = _ := by
      rw [show D = Matrix.diagonal fun ij =>
        ((hA.isHermitian.eigenvalues ij.1 * hB.isHermitian.eigenvalues ij.2 : Real) : Complex) by rfl]
      rw [trace_mul_cfc_diagonal]
      simp [Fintype.sum_prod_type]
end QEC.Semantics.FiniteMatrixEntropy
