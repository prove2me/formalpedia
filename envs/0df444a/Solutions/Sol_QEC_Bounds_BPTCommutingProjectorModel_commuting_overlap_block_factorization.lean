-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.commuting_overlap_block_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:40:41.72681+00:00
-- url     : https://prove2.me/submissions/a58b5a4c-916d-4c0c-9c54-ed2addabdfc0

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
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_starSubalgebra_module_isSemisimple
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_starSubalgebra_isotypicComponents_isInternal
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypic_commutant_matrix_factorization
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
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q)) :
    DirectSum.IsInternal (fun component : isotypicComponents (leftInteractionAlgebra P) B =>
      component.1) ∧
      ∀ component : isotypicComponents (leftInteractionAlgebra P) B,
        ∃ (n : Nat) (_ : NeZero n) (W : Submodule (leftInteractionAlgebra P) B)
          (hW : IsSimpleModule (leftInteractionAlgebra P) W)
          (e : component.1 ≃ₗ[leftInteractionAlgebra P] (Fin n → W)),
          (∀ a a' : A, ∀ (vector : component.1) (row : Fin n),
            e ((⟨leftInteractionCoefficient P a a',
              leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩ :
                leftInteractionAlgebra P) • vector) row =
              (⟨leftInteractionCoefficient P a a',
                leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩ :
                  leftInteractionAlgebra P) • e vector row) ∧
          (∀ c c' : C, ∃ matrix : Matrix (Fin n) (Fin n) Complex,
            ∀ (vector : component.1) (row : Fin n),
              e (rightInteractionCoefficientOnIsotypicComponent P Q hselfAdjoint hcommute
                component c c' vector) row =
                ∑ column, matrix row column • e vector column) := by
  letI : IsSemisimpleModule (leftInteractionAlgebra P) B :=
    starSubalgebra_module_isSemisimple (leftInteractionAlgebra P)
  constructor
  · exact starSubalgebra_isotypicComponents_isInternal (leftInteractionAlgebra P)
  · intro component
    letI complexModule : Module Complex component.1 :=
      starSubalgebraSubmoduleComplexModule (leftInteractionAlgebra P) component.1
    letI scalarTower : IsScalarTower Complex (leftInteractionAlgebra P) component.1 := by
      constructor
      intro scalar operator vector
      change ((algebraMap Complex (leftInteractionAlgebra P) scalar) * operator) • vector =
        (algebraMap Complex (leftInteractionAlgebra P) scalar) • (operator • vector)
      exact mul_smul _ _ _
    letI finiteDimensional : FiniteDimensional Complex component.1 :=
      FiniteDimensional.of_injective
        (starSubalgebraSubmoduleComplexInclusion (leftInteractionAlgebra P) component.1)
        Subtype.coe_injective
    letI finiteModule : Module.Finite (leftInteractionAlgebra P) component.1 :=
      @Module.Finite.of_restrictScalars_finite Complex (leftInteractionAlgebra P) component.1
        (inferInstance : Semiring Complex)
        (inferInstance : Semiring (leftInteractionAlgebra P))
        (inferInstance : AddCommMonoid component.1)
        complexModule (inferInstance : Module (leftInteractionAlgebra P) component.1)
        (inferInstance : SMul Complex (leftInteractionAlgebra P)) scalarTower
        (inferInstance : Module.Finite Complex component.1)
    obtain ⟨n, hn, W, _hWle, hW, he⟩ :=
      (IsIsotypic.isotypicComponents component.2).submodule_linearEquiv_fun
    rcases he with ⟨e⟩
    refine ⟨n, hn, W, hW, e, ?_, ?_⟩
    · intro a a' vector row
      rw [e.map_smul]
      rfl
    · intro c c'
      let right := rightInteractionCoefficientOnIsotypicComponent P Q hselfAdjoint hcommute
        component c c'
      let T : Module.End (leftInteractionAlgebra P) (Fin n → W) :=
        e.toLinearMap.comp (right.comp e.symm.toLinearMap)
      letI : IsSimpleModule (leftInteractionAlgebra P) W := hW
      obtain ⟨matrix, hmatrix⟩ :=
        isotypic_commutant_matrix_factorization (leftInteractionAlgebra P) W n T
      refine ⟨matrix, ?_⟩
      intro vector row
      have htransport : e (right vector) = T (e vector) := by
        simp [T, right]
      calc
        e (right vector) row = T (e vector) row := by rw [htransport]
        _ = ∑ column, matrix row column • e vector column := hmatrix (e vector) row
end QEC.Bounds.BPTCommutingProjectorModel
