-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.isotypic_commutant_matrix_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:24:11.508685+00:00
-- url     : https://prove2.me/submissions/94c080db-1158-4f30-91a5-6d7bb5603ac2

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorizationWithReference_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceReordering_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceTransport_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.mem_regionSubsystem_selected_iff
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.regionSubsystem_selected
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
attribute [local simp] QEC.Semantics.QuditSubsystem.registerFactorizationWithReference_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceReordering_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceTransport_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) [IsSimpleModule S W]
    (n : Nat) (T : Module.End S (Fin n → W)) :
    ∃ matrix : Matrix (Fin n) (Fin n) Complex,
      ∀ (vector : Fin n → W) (row : Fin n),
        T vector row = ∑ column, matrix row column • vector column := by
  letI complexModule : Module Complex W := starSubalgebraSubmoduleComplexModule S W
  letI scalarTower : IsScalarTower Complex S W := by
    constructor
    intro scalar operator vector
    change ((algebraMap Complex S scalar) * operator) • vector =
      (algebraMap Complex S scalar) • (operator • vector)
    exact mul_smul _ _ _
  letI smulComm : SMulCommClass S Complex W := by
    constructor
    intro operator scalar vector
    apply Subtype.ext
    change (operator : Semantics.Operator B) (scalar • (vector : B)) =
      scalar • (operator : Semantics.Operator B) vector
    exact (operator : Semantics.Operator B).map_smul scalar vector
  letI endAlgebra : Algebra Complex (Module.End S W) :=
    @Module.End.instAlgebra Complex S W _ _ _ complexModule
      (inferInstance : Module S W) smulComm (inferInstance : SMul Complex S) scalarTower
  letI finiteDimensional : FiniteDimensional Complex W :=
    FiniteDimensional.of_injective (starSubalgebraSubmoduleComplexInclusion S W)
      Subtype.coe_injective
  let entries : Matrix (Fin n) (Fin n) (Module.End S W) :=
    endVecRingEquivMatrixEnd (Fin n) S W T
  have hscalar : ∀ row column, ∃ scalar : Complex,
      algebraMap Complex (Module.End S W) scalar = entries row column := by
    intro row column
    exact (@IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed S W Complex
      (inferInstance : Field Complex) (inferInstance : Ring S)
      (inferInstance : Algebra Complex S) (inferInstance : AddCommGroup W)
      complexModule (inferInstance : Module S W) scalarTower
      (inferInstance : IsSimpleModule S W) finiteDimensional
      (inferInstance : IsAlgClosed Complex)).2 _
  choose matrix hmatrix using hscalar
  refine ⟨matrix, ?_⟩
  intro vector row
  have hentries : (endVecRingEquivMatrixEnd (Fin n) S W).symm entries = T := by
    simpa only [entries] using
      (endVecRingEquivMatrixEnd (Fin n) S W).symm_apply_apply T
  calc
    T vector row = ((endVecRingEquivMatrixEnd (Fin n) S W).symm entries) vector row := by
      rw [hentries]
    _ = ∑ column, entries row column (vector column) := rfl
    _ = ∑ column, matrix row column • vector column := by
      apply Finset.sum_congr rfl
      intro column _
      have hentry := congrArg
        (fun operator : Module.End S W => operator (vector column))
        (hmatrix row column).symm
      simpa using hentry
end QEC.Bounds.BPTCommutingProjectorModel
