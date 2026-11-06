-- Prove2me | solution 1 for QEC.Semantics.FiniteMatrixEntropy.cfc_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:49:42.841817+00:00
-- url     : https://prove2.me/submissions/0e801db6-2bf7-452e-b8dd-3fc791054d62

import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
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
namespace QEC.Semantics.FiniteMatrixEntropy
theorem _root_.solution {n : Type v} [Fintype n] [DecidableEq n]
    (d : n -> Real) (f : Real -> Real) :
    cfc f (Matrix.diagonal fun i => (d i : Complex)) =
      Matrix.diagonal fun i => (f (d i) : Complex) := by
  letI : ContinuousFunctionalCalculus Complex (n -> Complex) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : ContinuousFunctionalCalculus Real (n -> Complex) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  letI : ContinuousFunctionalCalculus Complex Complex IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : ContinuousFunctionalCalculus Real Complex IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  let a : n -> Complex := fun i => (d i : Complex)
  let phi : (n -> Complex) →⋆ₐ[Complex] Matrix n n Complex := diagonalStarAlgHom
  have hphi : Continuous phi := by
    change Continuous (fun x : n -> Complex => Matrix.diagonal x)
    exact continuous_id.matrix_diagonal
  have ha : IsSelfAdjoint a := by
    change star a = a
    ext i
    simp [a]
  have hphia : IsSelfAdjoint (phi a) := by
    dsimp [phi, diagonalStarAlgHom, a]
    change (Matrix.diagonal fun i => (d i : Complex)).IsHermitian
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    exact (Complex.im_eq_zero_iff_isSelfAdjoint _).mp (by simp)
  have hspectrum : (spectrum Real a).Finite := by
    rw [Pi.spectrum_eq]
    apply Set.finite_iUnion
    intro i
    refine (Set.finite_singleton (d i)).subset ?_
    intro x hx
    have hx' := CFC.spectrum_algebraMap_subset (A := Complex) (d i) hx
    simpa [a] using hx'
  have hcontinuity : ContinuousOn f (spectrum Real a) := hspectrum.continuousOn f
  have hunion : (⋃ i, spectrum Real (a i)).Finite := by
    rw [← Pi.spectrum_eq]
    exact hspectrum
  have hmap := phi.map_cfc f a hcontinuity hphi ha hphia
  calc
    cfc f (Matrix.diagonal fun i => (d i : Complex)) = phi (cfc f a) := by
      simpa [phi, diagonalStarAlgHom, a] using hmap.symm
    _ = phi (fun i => cfc f (a i)) := by
      rw [cfc_map_pi (R := Real) (S := Complex) (A := fun _ : n => Complex)
        (p := IsSelfAdjoint) (q := fun _ => IsSelfAdjoint) f a
        (hf := hunion.continuousOn f) (ha := ha) (ha' := by
        intro i
        change IsSelfAdjoint (a i)
        exact (Complex.im_eq_zero_iff_isSelfAdjoint _).mp (by simp [a]))]
    _ = Matrix.diagonal fun i => (f (d i) : Complex) := by
      change Matrix.diagonal (fun i => cfc f (a i)) = _
      congr 1
      funext i
      simpa [a] using (cfc_algebraMap (p := IsSelfAdjoint) (A := Complex)
        (R := Real) (d i) f)
end QEC.Semantics.FiniteMatrixEntropy
