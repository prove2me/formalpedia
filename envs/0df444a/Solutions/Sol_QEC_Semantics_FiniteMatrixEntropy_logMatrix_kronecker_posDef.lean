-- Prove2me | solution 1 for QEC.Semantics.FiniteMatrixEntropy.logMatrix_kronecker_posDef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:52:11.698441+00:00
-- url     : https://prove2.me/submissions/c6021290-0ec6-4231-abef-253488fea500

import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_cfc_diagonal
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
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



set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder Kronecker TensorProduct
noncomputable section
open QEC.Semantics.FiniteMatrixEntropy
set_option maxHeartbeats 2000000
namespace QEC.Semantics.FiniteMatrixEntropy
theorem _root_.solution {m : Type v} {n : Type w}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m Complex) (B : Matrix n n Complex)
    (hA : A.PosDef) (hB : B.PosDef) :
    logMatrix (A ⊗ₖ B) (hA.kronecker hB).isHermitian =
      logMatrix A hA.isHermitian ⊗ₖ 1 + 1 ⊗ₖ logMatrix B hB.isHermitian := by
  let UA : Matrix.unitaryGroup m Complex := hA.isHermitian.eigenvectorUnitary
  let UB : Matrix.unitaryGroup n Complex := hB.isHermitian.eigenvectorUnitary
  let U : Matrix.unitaryGroup (m × n) Complex :=
    ⟨(UA : Matrix m m Complex) ⊗ₖ (UB : Matrix n n Complex),
      Matrix.kronecker_mem_unitary UA.property UB.property⟩
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
    have hstar : star ((UA : Matrix m m Complex) ⊗ₖ (UB : Matrix n n Complex)) =
        star (UA : Matrix m m Complex) ⊗ₖ star (UB : Matrix n n Complex) := by
      simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]
    rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]
    change
      ((UA : Matrix m m Complex) ⊗ₖ (UB : Matrix n n Complex)) *
          (Matrix.diagonal (Complex.ofReal ∘ hA.isHermitian.eigenvalues) ⊗ₖ
            Matrix.diagonal (Complex.ofReal ∘ hB.isHermitian.eigenvalues)) *
          (star (UA : Matrix m m Complex) ⊗ₖ star (UB : Matrix n n Complex)) =
        ((UA : Matrix m m Complex) ⊗ₖ (UB : Matrix n n Complex)) * D *
          star ((UA : Matrix m m Complex) ⊗ₖ (UB : Matrix n n Complex))
    rw [Matrix.diagonal_kronecker_diagonal, hstar]
    simp [D, Complex.ofReal_mul]
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
  have hmiddle : cfc Real.log D =
      Matrix.diagonal (fun i => (Real.log (hA.isHermitian.eigenvalues i) : Complex)) ⊗ₖ 1 +
        1 ⊗ₖ Matrix.diagonal (fun j => (Real.log (hB.isHermitian.eigenvalues j) : Complex)) := by
    rw [show D = Matrix.diagonal fun ij : m × n =>
      ((hA.isHermitian.eigenvalues ij.1 * hB.isHermitian.eigenvalues ij.2 : Real) : Complex) by rfl]
    rw [cfc_diagonal]
    rw [← Matrix.diagonal_one (n := n), ← Matrix.diagonal_one (n := m)]
    rw [Matrix.diagonal_kronecker_diagonal, Matrix.diagonal_kronecker_diagonal]
    ext ij kl
    rcases ij with ⟨i, j⟩
    rcases kl with ⟨i', j'⟩
    by_cases hi : i = i'
    · subst i'
      by_cases hj : j = j'
      · subst j'
        simp only [Matrix.add_apply, Matrix.diagonal_apply_eq]
        rw [Real.log_mul (ne_of_gt (hA.eigenvalues_pos i))
          (ne_of_gt (hB.eigenvalues_pos j))]
        rw [Complex.ofReal_add]
        simp
      · simp [Matrix.diagonal, hj]
    · simp [Matrix.diagonal, hi]
  have hlogA : logMatrix A hA.isHermitian =
      (UA : Matrix m m Complex) *
        Matrix.diagonal (fun i => (Real.log (hA.isHermitian.eigenvalues i) : Complex)) *
        star (UA : Matrix m m Complex) := by
    change hA.isHermitian.cfc Real.log = _
    rfl
  have hlogB : logMatrix B hB.isHermitian =
      (UB : Matrix n n Complex) *
        Matrix.diagonal (fun j => (Real.log (hB.isHermitian.eigenvalues j) : Complex)) *
        star (UB : Matrix n n Complex) := by
    change hB.isHermitian.cfc Real.log = _
    rfl
  have hUA : (UA : Matrix m m Complex) * star (UA : Matrix m m Complex) = 1 :=
    Unitary.coe_mul_star_self UA
  have hUB : (UB : Matrix n n Complex) * star (UB : Matrix n n Complex) = 1 :=
    Unitary.coe_mul_star_self UB
  have hUstar : star ((UA : Matrix m m Complex) ⊗ₖ (UB : Matrix n n Complex)) =
      star (UA : Matrix m m Complex) ⊗ₖ star (UB : Matrix n n Complex) := by
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]
  rw [hlog, hmiddle, hlogA, hlogB]
  simp only [U, Matrix.mul_add, Matrix.add_mul]
  rw [hUstar]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.mul_one]
  rw [hUB, hUA]
end QEC.Semantics.FiniteMatrixEntropy
