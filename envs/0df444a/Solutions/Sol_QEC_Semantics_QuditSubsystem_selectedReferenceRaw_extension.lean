-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.selectedReferenceRaw_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:57:05.09853+00:00
-- url     : https://prove2.me/submissions/ba8b5056-f472-4490-bac1-15558445017c

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Theorems.Thm_QEC_Semantics_QuditSubsystem_smul_tensorMap_rankOne
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceReordering_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorizationWithReference_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceTransport_apply_tmul
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
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_registerFactorization_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne
import Theorems.Thm_QEC_Semantics_QuditSubsystem_linearMap_ext_of_rankOne_basis
import Theorems.Thm_QEC_Semantics_QuditSubsystem_partialTraceRightRaw_rankOne_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorization_apply_basis
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


attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceReordering_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.registerFactorizationWithReference_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceTransport_apply_tmul

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v w
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
set_option maxHeartbeats 800000
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S : QuditSubsystem q)
    (Ref : Type u) [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref]
    [FiniteQuantumSystem Ref] (A : Operator (Qudit.QuditRegister q))
    (r s : Ref) :
    partialTraceRightRaw (CompositeSystem S.selectedSystem Ref) S.complementSystem
      ((S.selectedReferenceTransport Ref).conjOperator
        (TensorProduct.map A (InnerProductSpace.rankOne Complex r s).toLinearMap)) =
      TensorProduct.map (S.selectedPartialTraceFromRegister A)
        (InnerProductSpace.rankOne Complex r s).toLinearMap := by
  classical
  change S.selectedReferenceRaw Ref
    (TensorProduct.map A (InnerProductSpace.rankOne Complex r s).toLinearMap) = _
  let Phi : Operator (Qudit.QuditRegister q) →ₗ[Complex]
      Operator (CompositeSystem S.selectedSystem Ref) :=
    {
    toFun := fun Z => S.selectedReferenceRaw Ref
      (TensorProduct.map Z (InnerProductSpace.rankOne Complex r s).toLinearMap)
    map_add' := by
      intro X Y
      rw [TensorProduct.map_add_left]
      exact (S.selectedReferenceRaw Ref).map_add _ _
    map_smul' := by
      intro a X
      rw [TensorProduct.map_smul_left]
      exact (S.selectedReferenceRaw Ref).map_smul a _
    }
  let Psi : Operator (Qudit.QuditRegister q) →ₗ[Complex]
      Operator (CompositeSystem S.selectedSystem Ref) :=
    {
    toFun := fun Z => TensorProduct.map (S.selectedPartialTraceFromRegister Z)
      (InnerProductSpace.rankOne Complex r s).toLinearMap
    map_add' := by
      intro X Y
      simp [TensorProduct.map_add_left]
    map_smul' := by
      intro a X
      simp [TensorProduct.map_smul_left]
    }
  have hmaps : Phi = Psi := by
    let b := EuclideanSpace.basisFun (Qudit.Label q) Complex
    apply linearMap_ext_of_rankOne_basis b Phi Psi
    intro x y
    dsimp [Phi, Psi]
    change partialTraceRightRaw (CompositeSystem S.selectedSystem Ref) S.complementSystem
      ((S.selectedReferenceTransport Ref).conjOperator
        (TensorProduct.map
          (InnerProductSpace.rankOne Complex (b x) (b y)).toLinearMap
          (InnerProductSpace.rankOne Complex r s).toLinearMap)) = _
    rw [tensorMap_rankOne]
    rw [conjOperator_rankOne]
    have hxr : S.selectedReferenceTransport Ref ((b x) ⊗ₜ[Complex] r) =
        S.selectedReferenceReordering Ref ((S.registerFactorization (b x)) ⊗ₜ[Complex] r) := rfl
    have hys : S.selectedReferenceTransport Ref ((b y) ⊗ₜ[Complex] s) =
        S.selectedReferenceReordering Ref ((S.registerFactorization (b y)) ⊗ₜ[Complex] s) := rfl
    have htransport :
        (InnerProductSpace.rankOne Complex
          (S.selectedReferenceTransport Ref ((b x) ⊗ₜ[Complex] r))
          (S.selectedReferenceTransport Ref ((b y) ⊗ₜ[Complex] s))).toLinearMap =
        (InnerProductSpace.rankOne Complex
          (S.selectedReferenceReordering Ref
            ((S.registerFactorization (b x)) ⊗ₜ[Complex] r))
          (S.selectedReferenceReordering Ref
            ((S.registerFactorization (b y)) ⊗ₜ[Complex] s))).toLinearMap := by
      rfl
    rw [htransport]
    let ux : CompositeSystem (CompositeSystem S.selectedSystem Ref) S.complementSystem :=
      S.selectedReferenceReordering Ref
        ((S.registerFactorization (b x)) ⊗ₜ[Complex] r)
    let uy : CompositeSystem (CompositeSystem S.selectedSystem Ref) S.complementSystem :=
      S.selectedReferenceReordering Ref
        ((S.registerFactorization (b y)) ⊗ₜ[Complex] s)
    let vx : CompositeSystem (CompositeSystem S.selectedSystem Ref) S.complementSystem :=
      S.selectedReferenceReordering Ref
        (((EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
          (S.splitLabel x).1) ⊗ₜ[Complex]
          (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
            (S.splitLabel x).2)) ⊗ₜ[Complex] r)
    let vy : CompositeSystem (CompositeSystem S.selectedSystem Ref) S.complementSystem :=
      S.selectedReferenceReordering Ref
        (((EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
          (S.splitLabel y).1) ⊗ₜ[Complex]
          (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
            (S.splitLabel y).2)) ⊗ₜ[Complex] s)
    change partialTraceRightRaw (CompositeSystem S.selectedSystem Ref) S.complementSystem
      (InnerProductSpace.rankOne Complex ux uy).toLinearMap = _
    have hfactorX : ux = vx := by
      dsimp [ux, vx]
      exact congrArg
        (fun z : S.factorizedSystem =>
          S.selectedReferenceReordering Ref (z ⊗ₜ[Complex] r))
        (S.registerFactorization_apply_basis x)
    have hfactorY : uy = vy := by
      dsimp [uy, vy]
      exact congrArg
        (fun z : S.factorizedSystem =>
          S.selectedReferenceReordering Ref (z ⊗ₜ[Complex] s))
        (S.registerFactorization_apply_basis y)
    have hfactorRank :
        (InnerProductSpace.rankOne Complex ux uy).toLinearMap =
          (InnerProductSpace.rankOne Complex vx vy).toLinearMap := by
      rw [hfactorX, hfactorY]
    refine (congrArg
      (partialTraceRightRaw (CompositeSystem S.selectedSystem Ref) S.complementSystem)
      hfactorRank).trans ?_
    let wx : CompositeSystem (CompositeSystem S.selectedSystem Ref) S.complementSystem :=
      ((EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
        (S.splitLabel x).1) ⊗ₜ[Complex] r) ⊗ₜ[Complex]
        (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
          (S.splitLabel x).2)
    let wy : CompositeSystem (CompositeSystem S.selectedSystem Ref) S.complementSystem :=
      ((EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
        (S.splitLabel y).1) ⊗ₜ[Complex] s) ⊗ₜ[Complex]
        (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex
          (S.splitLabel y).2)
    have hreordering :
        (InnerProductSpace.rankOne Complex vx vy).toLinearMap =
          (InnerProductSpace.rankOne Complex wx wy).toLinearMap := by
      rfl
    refine (congrArg
      (partialTraceRightRaw (CompositeSystem S.selectedSystem Ref) S.complementSystem)
      hreordering).trans ?_
    dsimp [wx, wy]
    rw [partialTraceRightRaw_rankOne_tmul]
    let mx : S.selectedSystem :=
      EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex (S.splitLabel x).1
    let my : S.selectedSystem :=
      EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex (S.splitLabel y).1
    let bx : S.complementSystem :=
      EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex (S.splitLabel x).2
    let by_ : S.complementSystem :=
      EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex (S.splitLabel y).2
    have hselected :
        S.selectedPartialTraceFromRegister
          (InnerProductSpace.rankOne Complex (b x) (b y)).toLinearMap =
          (inner Complex by_ bx) • (InnerProductSpace.rankOne Complex mx my).toLinearMap := by
      simp only [selectedPartialTraceFromRegister, QuantumChannel.comp_apply,
        QuantumChannel.unitaryConj_apply]
      rw [conjOperator_rankOne S.registerFactorization]
      change partialTraceRightRaw S.selectedSystem S.complementSystem
        (InnerProductSpace.rankOne Complex
          ((S.registerFactorization (b x)))
          ((S.registerFactorization (b y)))).toLinearMap = _
      have hfactor :
          (InnerProductSpace.rankOne Complex
            (S.registerFactorization (b x))
            (S.registerFactorization (b y))).toLinearMap =
          (InnerProductSpace.rankOne Complex
            (mx ⊗ₜ[Complex] bx) (my ⊗ₜ[Complex] by_)).toLinearMap := by
        dsimp [mx, my, bx, by_]
        rw [S.registerFactorization_apply_basis x,
          S.registerFactorization_apply_basis y]
      refine (congrArg
        (partialTraceRightRaw S.selectedSystem S.complementSystem) hfactor).trans ?_
      rw [partialTraceRightRaw_rankOne_tmul]
    rw [hselected]
    change (inner Complex by_ bx) •
        (InnerProductSpace.rankOne Complex (mx ⊗ₜ[Complex] r)
          (my ⊗ₜ[Complex] s)).toLinearMap =
      TensorProduct.map ((inner Complex by_ bx) •
        (InnerProductSpace.rankOne Complex mx my).toLinearMap)
        (InnerProductSpace.rankOne Complex r s).toLinearMap
    exact smul_tensorMap_rankOne (inner Complex by_ bx) mx my r s
  exact congrArg (fun F : Operator (Qudit.QuditRegister q) →ₗ[Complex]
    Operator (CompositeSystem S.selectedSystem Ref) => F A) hmaps
end QEC.Semantics.QuditSubsystem
