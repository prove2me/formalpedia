-- Prove2me | solution 1 for QEC.Semantics.DensityOperator.vonNeumannEntropy_subadditive_bipartite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:01:29.149512+00:00
-- url     : https://prove2.me/submissions/165be352-4041-40bb-bfb2-59bf184bfd50

import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_posSemidef_toMatrix_of_isPositive
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_realTrace_toMatrix
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_realTrace_joint_mul_kronecker_right_matrix
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_realTrace_joint_mul_kronecker_left_matrix
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_kronecker_posDef
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_tendsto_realTrace_mul_log_epsilonRegularize
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_trace_eq_one_of_realTrace_eq_one
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_realTrace_add
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_realTrace_sub
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_realTrace_mul_log2Matrix_eq_inv_log_two_mul
import Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_eq_neg_realTrace_mul_log2Matrix_of_basis
import Theorems.Thm_QEC_Semantics_DensityOperator_leftMarginal_toOperator_eq_partialTraceLeftRaw
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_klein_trace_inequality
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_realTrace_epsilonRegularize
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
open QEC.Semantics.DensityOperator
set_option maxHeartbeats 3000000
namespace QEC.Semantics.DensityOperator
theorem _root_.solution
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] (rho : DensityOperator (CompositeSystem H K)) :
    rho.vonNeumannEntropy <=
      (rightMarginal rho).vonNeumannEntropy + (leftMarginal rho).vonNeumannEntropy := by
  let bH : OrthonormalBasis (ULift.{u} (Fin (Module.finrank Complex H))) Complex H :=
    (stdOrthonormalBasis Complex H).reindex Equiv.ulift.symm
  let bK : OrthonormalBasis (ULift.{u} (Fin (Module.finrank Complex K))) Complex K :=
    (stdOrthonormalBasis Complex K).reindex Equiv.ulift.symm
  let bHK := bH.tensorProduct bK
  let A := rho.toOperator.toMatrix bHK.toBasis bHK.toBasis
  let B := (rightMarginal rho).toOperator.toMatrix bH.toBasis bH.toBasis
  let C := (leftMarginal rho).toOperator.toMatrix bK.toBasis bK.toBasis
  have hA : A.PosSemidef := by
    dsimp [A]
    exact FiniteMatrixEntropy.posSemidef_toMatrix_of_isPositive bHK rho.toOperator rho.positive
  have hB : B.PosSemidef := by
    dsimp [B]
    exact FiniteMatrixEntropy.posSemidef_toMatrix_of_isPositive bH
      (rightMarginal rho).toOperator (rightMarginal rho).positive
  have hC : C.PosSemidef := by
    dsimp [C]
    exact FiniteMatrixEntropy.posSemidef_toMatrix_of_isPositive bK
      (leftMarginal rho).toOperator (leftMarginal rho).positive
  have hAtrace : FiniteMatrixEntropy.realTrace A = 1 := by
    dsimp [A]
    rw [FiniteMatrixEntropy.realTrace_toMatrix]
    rw [rho.trace_one]
    norm_num
  have hBtrace : FiniteMatrixEntropy.realTrace B = 1 := by
    dsimp [B]
    rw [FiniteMatrixEntropy.realTrace_toMatrix]
    rw [(rightMarginal rho).trace_one]
    norm_num
  have hCtrace : FiniteMatrixEntropy.realTrace C = 1 := by
    dsimp [C]
    rw [FiniteMatrixEntropy.realTrace_toMatrix]
    rw [(leftMarginal rho).trace_one]
    norm_num
  have hregularized (epsilon : Real) (hepsilon : 0 < epsilon) :
      FiniteMatrixEntropy.realTrace
          (B * FiniteMatrixEntropy.logMatrix (FiniteMatrixEntropy.epsilonRegularize B epsilon)
            (FiniteMatrixEntropy.epsilonRegularize_posDef B hB hepsilon).isHermitian) +
        FiniteMatrixEntropy.realTrace
          (C * FiniteMatrixEntropy.logMatrix (FiniteMatrixEntropy.epsilonRegularize C epsilon)
            (FiniteMatrixEntropy.epsilonRegularize_posDef C hC hepsilon).isHermitian) <=
        FiniteMatrixEntropy.realTrace
          (A * FiniteMatrixEntropy.logMatrix A hA.isHermitian) := by
    have hBe : (FiniteMatrixEntropy.epsilonRegularize B epsilon).PosDef :=
      FiniteMatrixEntropy.epsilonRegularize_posDef B hB hepsilon
    have hCe : (FiniteMatrixEntropy.epsilonRegularize C epsilon).PosDef :=
      FiniteMatrixEntropy.epsilonRegularize_posDef C hC hepsilon
    have hP :
        (FiniteMatrixEntropy.epsilonRegularize B epsilon ⊗ₖ
          FiniteMatrixEntropy.epsilonRegularize C epsilon).PosDef := hBe.kronecker hCe
    have hBeTrace : FiniteMatrixEntropy.realTrace
        (FiniteMatrixEntropy.epsilonRegularize B epsilon) = 1 :=
      FiniteMatrixEntropy.realTrace_epsilonRegularize B hB hBtrace hepsilon
    have hCeTrace : FiniteMatrixEntropy.realTrace
        (FiniteMatrixEntropy.epsilonRegularize C epsilon) = 1 :=
      FiniteMatrixEntropy.realTrace_epsilonRegularize C hC hCtrace hepsilon
    have hBeTraceComplex : (FiniteMatrixEntropy.epsilonRegularize B epsilon).trace = 1 :=
      FiniteMatrixEntropy.trace_eq_one_of_realTrace_eq_one
        (FiniteMatrixEntropy.epsilonRegularize B epsilon) hBe.posSemidef hBeTrace
    have hCeTraceComplex : (FiniteMatrixEntropy.epsilonRegularize C epsilon).trace = 1 :=
      FiniteMatrixEntropy.trace_eq_one_of_realTrace_eq_one
        (FiniteMatrixEntropy.epsilonRegularize C epsilon) hCe.posSemidef hCeTrace
    have hPTrace : FiniteMatrixEntropy.realTrace
        (FiniteMatrixEntropy.epsilonRegularize B epsilon ⊗ₖ
          FiniteMatrixEntropy.epsilonRegularize C epsilon) = 1 := by
      unfold FiniteMatrixEntropy.realTrace
      rw [Matrix.trace_kronecker, hBeTraceComplex, hCeTraceComplex]
      norm_num
    have hBraw : (rightMarginal rho).toOperator =
        partialTraceRightRaw H K rho.toOperator := by
      rfl
    have hCraw : (leftMarginal rho).toOperator =
        FiniteMatrixEntropy.partialTraceLeftRaw H K rho.toOperator :=
      leftMarginal_toOperator_eq_partialTraceLeftRaw rho
    have hright : FiniteMatrixEntropy.realTrace
        (A * (FiniteMatrixEntropy.logMatrix (FiniteMatrixEntropy.epsilonRegularize B epsilon)
          hBe.isHermitian ⊗ₖ (1 : Matrix _ _ Complex))) =
        FiniteMatrixEntropy.realTrace
          (B * FiniteMatrixEntropy.logMatrix (FiniteMatrixEntropy.epsilonRegularize B epsilon)
            hBe.isHermitian) := by
      have hrightRaw :=
        FiniteMatrixEntropy.realTrace_joint_mul_kronecker_right_matrix bH bK rho.toOperator
          (FiniteMatrixEntropy.logMatrix (FiniteMatrixEntropy.epsilonRegularize B epsilon)
            hBe.isHermitian)
      rw [← hBraw] at hrightRaw
      simpa only [A, B] using hrightRaw
    have hleft : FiniteMatrixEntropy.realTrace
        (A * ((1 : Matrix _ _ Complex) ⊗ₖ
          FiniteMatrixEntropy.logMatrix (FiniteMatrixEntropy.epsilonRegularize C epsilon)
            hCe.isHermitian)) =
        FiniteMatrixEntropy.realTrace
          (C * FiniteMatrixEntropy.logMatrix (FiniteMatrixEntropy.epsilonRegularize C epsilon)
            hCe.isHermitian) := by
      have hleftRaw :=
        FiniteMatrixEntropy.realTrace_joint_mul_kronecker_left_matrix bH bK rho.toOperator
          (FiniteMatrixEntropy.logMatrix (FiniteMatrixEntropy.epsilonRegularize C epsilon)
            hCe.isHermitian)
      rw [← hCraw] at hleftRaw
      simpa only [A, C] using hleftRaw
    have hcross : FiniteMatrixEntropy.realTrace
        (A * FiniteMatrixEntropy.logMatrix
          (FiniteMatrixEntropy.epsilonRegularize B epsilon ⊗ₖ
            FiniteMatrixEntropy.epsilonRegularize C epsilon) hP.isHermitian) =
        FiniteMatrixEntropy.realTrace
          (B * FiniteMatrixEntropy.logMatrix (FiniteMatrixEntropy.epsilonRegularize B epsilon)
            hBe.isHermitian) +
          FiniteMatrixEntropy.realTrace
            (C * FiniteMatrixEntropy.logMatrix (FiniteMatrixEntropy.epsilonRegularize C epsilon)
              hCe.isHermitian) := by
      rw [FiniteMatrixEntropy.logMatrix_kronecker_posDef _ _ hBe hCe, Matrix.mul_add,
        FiniteMatrixEntropy.realTrace_add, hright, hleft]
    have hKlein := FiniteMatrixEntropy.klein_trace_inequality A
      (FiniteMatrixEntropy.epsilonRegularize B epsilon ⊗ₖ
        FiniteMatrixEntropy.epsilonRegularize C epsilon) hA hP
    have hdiff : FiniteMatrixEntropy.realTrace
        (A - (FiniteMatrixEntropy.epsilonRegularize B epsilon ⊗ₖ
          FiniteMatrixEntropy.epsilonRegularize C epsilon)) = 0 := by
      rw [FiniteMatrixEntropy.realTrace_sub, hAtrace, hPTrace]
      norm_num
    rw [hdiff] at hKlein
    unfold FiniteMatrixEntropy.relativeEntropy at hKlein
    rw [Matrix.mul_sub, FiniteMatrixEntropy.realTrace_sub, hcross] at hKlein
    linarith
  have hlimit : Filter.Tendsto (fun k : Nat =>
      FiniteMatrixEntropy.realTrace
        (B * FiniteMatrixEntropy.logMatrix
          (FiniteMatrixEntropy.epsilonRegularize B (1 / ((k : Real) + 1)))
          (FiniteMatrixEntropy.epsilonRegularize_posDef B hB (by positivity)).isHermitian) +
      FiniteMatrixEntropy.realTrace
        (C * FiniteMatrixEntropy.logMatrix
          (FiniteMatrixEntropy.epsilonRegularize C (1 / ((k : Real) + 1)))
          (FiniteMatrixEntropy.epsilonRegularize_posDef C hC (by positivity)).isHermitian))
      Filter.atTop
      (nhds
        (FiniteMatrixEntropy.realTrace (B * FiniteMatrixEntropy.logMatrix B hB.isHermitian) +
          FiniteMatrixEntropy.realTrace (C * FiniteMatrixEntropy.logMatrix C hC.isHermitian))) :=
    (FiniteMatrixEntropy.tendsto_realTrace_mul_log_epsilonRegularize B hB).add
      (FiniteMatrixEntropy.tendsto_realTrace_mul_log_epsilonRegularize C hC)
  have hnatural :
      FiniteMatrixEntropy.realTrace (B * FiniteMatrixEntropy.logMatrix B hB.isHermitian) +
        FiniteMatrixEntropy.realTrace (C * FiniteMatrixEntropy.logMatrix C hC.isHermitian) <=
        FiniteMatrixEntropy.realTrace (A * FiniteMatrixEntropy.logMatrix A hA.isHermitian) := by
    apply le_of_tendsto' hlimit
    intro k
    exact hregularized (1 / ((k : Real) + 1)) (by positivity)
  have hEntropyA : rho.vonNeumannEntropy =
      -((Real.log 2)⁻¹ *
        FiniteMatrixEntropy.realTrace (A * FiniteMatrixEntropy.logMatrix A hA.isHermitian)) := by
    calc
      rho.vonNeumannEntropy =
          -FiniteMatrixEntropy.realTrace
            (A * FiniteMatrixEntropy.log2Matrix A hA.isHermitian) := by
        simpa only [A] using rho.vonNeumannEntropy_eq_neg_realTrace_mul_log2Matrix_of_basis bHK
      _ = _ := by rw [FiniteMatrixEntropy.realTrace_mul_log2Matrix_eq_inv_log_two_mul]
  have hEntropyB : (rightMarginal rho).vonNeumannEntropy =
      -((Real.log 2)⁻¹ *
        FiniteMatrixEntropy.realTrace (B * FiniteMatrixEntropy.logMatrix B hB.isHermitian)) := by
    calc
      (rightMarginal rho).vonNeumannEntropy =
          -FiniteMatrixEntropy.realTrace
            (B * FiniteMatrixEntropy.log2Matrix B hB.isHermitian) := by
        simpa only [B] using
          (rightMarginal rho).vonNeumannEntropy_eq_neg_realTrace_mul_log2Matrix_of_basis bH
      _ = _ := by rw [FiniteMatrixEntropy.realTrace_mul_log2Matrix_eq_inv_log_two_mul]
  have hEntropyC : (leftMarginal rho).vonNeumannEntropy =
      -((Real.log 2)⁻¹ *
        FiniteMatrixEntropy.realTrace (C * FiniteMatrixEntropy.logMatrix C hC.isHermitian)) := by
    calc
      (leftMarginal rho).vonNeumannEntropy =
          -FiniteMatrixEntropy.realTrace
            (C * FiniteMatrixEntropy.log2Matrix C hC.isHermitian) := by
        simpa only [C] using
          (leftMarginal rho).vonNeumannEntropy_eq_neg_realTrace_mul_log2Matrix_of_basis bK
      _ = _ := by rw [FiniteMatrixEntropy.realTrace_mul_log2Matrix_eq_inv_log_two_mul]
  have hinv : 0 <= (Real.log 2)⁻¹ := by
    exact inv_nonneg.mpr (le_of_lt (Real.log_pos (by norm_num)))
  have hscaled := mul_le_mul_of_nonneg_left hnatural hinv
  rw [hEntropyA, hEntropyB, hEntropyC]
  nlinarith
end QEC.Semantics.DensityOperator
