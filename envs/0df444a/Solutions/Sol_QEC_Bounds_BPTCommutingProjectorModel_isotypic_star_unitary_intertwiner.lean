-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.isotypic_star_unitary_intertwiner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:37:38.662253+00:00
-- url     : https://prove2.me/submissions/c0a47a60-26b5-422a-8804-69e47126c495

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
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_gram_commutes_of_star_intertwines
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicLeftAction_adjoint_QECertChecked
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicLeftActionOnCopies_adjoint
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


section
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
private theorem unitary_star_intertwiner_of_linearEquiv
    {R H K : Type u} [InvolutiveStar R]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteDimensional Complex H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteDimensional Complex K]
    (rhoH : R → Module.End Complex H) (rhoK : R → Module.End Complex K)
    (hH : ∀ r, LinearMap.adjoint (rhoH r) = rhoH (star r))
    (hK : ∀ r, LinearMap.adjoint (rhoK r) = rhoK (star r))
    (e : H ≃ₗ[Complex] K)
    (hintertwines : ∀ r, e.toLinearMap.comp (rhoH r) = (rhoK r).comp e.toLinearMap) :
    ∃ U : Semantics.UnitaryTransport H K,
      ∀ r, U.toLinearEquiv.toLinearMap.comp (rhoH r) =
        (rhoK r).comp U.toLinearEquiv.toLinearMap := by
  let f : H →L[Complex] K := e.toContinuousLinearEquiv.toContinuousLinearMap
  let G : H →L[Complex] H := f.adjoint.comp f
  have hf_intertwines : ∀ r, f.toLinearMap.comp (rhoH r) =
      (rhoK r).comp f.toLinearMap := by
    intro r
    simpa [f] using hintertwines r
  have hf_injective : Function.Injective f := by
    intro x y hxy
    exact e.injective hxy
  have hG_injective : Function.Injective G :=
    (f.adjoint_comp_self_injective_iff).mpr hf_injective
  let gEquiv : H ≃ₗ[Complex] H := LinearEquiv.ofBijective G.toLinearMap
    ⟨hG_injective, LinearMap.injective_iff_surjective.mp hG_injective⟩
  let gContinuous : H ≃L[Complex] H := gEquiv.toContinuousLinearEquiv
  have hgContinuous : gContinuous.toContinuousLinearMap = G := by
    ext x
    rfl
  have hG_unit : IsUnit G := by
    refine ⟨gContinuous.toUnit, ?_⟩
    exact hgContinuous.symm
  have hG_nonneg : 0 ≤ G :=
    (ContinuousLinearMap.nonneg_iff_isPositive G).mpr
      (ContinuousLinearMap.isPositive_adjoint_comp_self f)
  have hG_commutes : ∀ r, Commute G (LinearMap.toContinuousLinearMap (rhoH r)) := by
    intro r
    have hlinear := gram_commutes_of_star_intertwines rhoH rhoK hH hK
      f.toLinearMap hf_intertwines r
    rw [ContinuousLinearMap.adjoint_toLinearMap] at hlinear
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun operator : Module.End Complex H => operator x) hlinear.eq
  let p : H →L[Complex] H := CFC.sqrt G
  have hp_sq : p.comp p = G := by
    change p * p = G
    simpa [p] using CFC.sqrt_mul_sqrt_self G hG_nonneg
  have hp_self : p.adjoint = p := by
    change star p = p
    exact (CFC.sqrt_nonneg G).isSelfAdjoint
  have hp_commutes : ∀ r, Commute p (LinearMap.toContinuousLinearMap (rhoH r)) := by
    intro r
    simpa [p, CFC.sqrt_eq_cfc] using (hG_commutes r).cfc_nnreal NNReal.sqrt
  have hp_unit : IsUnit p := (CFC.isUnit_sqrt_iff G hG_nonneg).mpr hG_unit
  rcases hp_unit with ⟨pUnit, hpUnit⟩
  let pInv : H →L[Complex] H := (↑(pUnit⁻¹) : H →L[Complex] H)
  have hp_mul_pInv : p.comp pInv = 1 := by
    simpa [pInv, ContinuousLinearMap.mul_def, hpUnit] using pUnit.val_inv
  have hpInv_adjoint_comp_p : pInv.adjoint.comp p = 1 := by
    have h := congrArg ContinuousLinearMap.adjoint hp_mul_pInv
    simpa [ContinuousLinearMap.adjoint_comp, hp_self, ContinuousLinearMap.adjoint_one] using h
  have hpInv_commutes : ∀ r, Commute pInv (LinearMap.toContinuousLinearMap (rhoH r)) := by
    intro r
    have hunit : Commute (↑pUnit : H →L[Complex] H)
        (LinearMap.toContinuousLinearMap (rhoH r)) := by
      simpa [hpUnit] using hp_commutes r
    simpa [pInv] using hunit.units_inv_left
  let pEquiv : H ≃L[Complex] H := ContinuousLinearEquiv.unitsEquiv Complex H pUnit
  let uEquiv : H ≃L[Complex] K := pEquiv.symm.trans e.toContinuousLinearEquiv
  have hu_eq : uEquiv.toContinuousLinearMap = f.comp pInv := by
    ext x
    rfl
  have hu_adjoint_comp :
      uEquiv.toContinuousLinearMap.adjoint.comp uEquiv.toContinuousLinearMap = 1 := by
    rw [hu_eq, ContinuousLinearMap.adjoint_comp]
    ext x
    change pInv.adjoint (f.adjoint (f (pInv x))) = x
    calc
      pInv.adjoint (f.adjoint (f (pInv x))) = pInv.adjoint (G (pInv x)) := rfl
      _ = pInv.adjoint ((p.comp p) (pInv x)) := by rw [hp_sq]
      _ = ((pInv.adjoint.comp p).comp (p.comp pInv)) x := by rfl
      _ = x := by simp [hpInv_adjoint_comp_p, hp_mul_pInv]
  have hu_inner : ∀ x y : H,
      inner Complex (uEquiv x) (uEquiv y) = inner Complex x y := by
    simpa using
      (uEquiv.toContinuousLinearMap.inner_map_map_iff_adjoint_comp_self).mpr hu_adjoint_comp
  let U : Semantics.UnitaryTransport H K :=
    { toLinearEquiv := uEquiv.toLinearEquiv
      map_inner := by
        intro x y
        simpa using hu_inner x y }
  refine ⟨U, ?_⟩
  have hu_linear : uEquiv.toLinearEquiv.toLinearMap =
      f.toLinearMap.comp pInv.toLinearMap := by
    exact congrArg ContinuousLinearMap.toLinearMap hu_eq
  have hpInv_linear_commutes : ∀ r, Commute pInv.toLinearMap (rhoH r) := by
    intro r
    change pInv.toLinearMap.comp (rhoH r) = (rhoH r).comp pInv.toLinearMap
    apply LinearMap.ext
    intro x
    simpa using congrArg (fun operator : H →L[Complex] H => operator x) (hpInv_commutes r).eq
  intro r
  change uEquiv.toLinearEquiv.toLinearMap.comp (rhoH r) =
    (rhoK r).comp uEquiv.toLinearEquiv.toLinearMap
  rw [hu_linear]
  calc
    (f.toLinearMap.comp pInv.toLinearMap).comp (rhoH r) =
        f.toLinearMap.comp (pInv.toLinearMap.comp (rhoH r)) := by
      rw [LinearMap.comp_assoc]
    _ = f.toLinearMap.comp ((rhoH r).comp pInv.toLinearMap) := by
      exact congrArg (fun operator : Module.End Complex H => f.toLinearMap.comp operator)
        (hpInv_linear_commutes r).eq
    _ = (f.toLinearMap.comp (rhoH r)).comp pInv.toLinearMap := by
      rw [← LinearMap.comp_assoc]
    _ = ((rhoK r).comp f.toLinearMap).comp pInv.toLinearMap := by
      rw [hf_intertwines r]
    _ = (rhoK r).comp (f.toLinearMap.comp pInv.toLinearMap) := by
      rw [LinearMap.comp_assoc]
end BPTCommutingProjectorModel
end Bounds
end QEC
end
end

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
    (component : isotypicComponents S B) (n : Nat) (W : Submodule S B)
    (e : component.1 ≃ₗ[S] (Fin n → W)) :
    ∃ U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (PiLp 2 (fun _ : Fin n => W.restrictScalars Complex)),
      ∀ operator : S,
        U.toLinearEquiv.toLinearMap.comp (isotypicLeftAction S component operator) =
          (isotypicLeftActionOnCopies S W n operator).comp U.toLinearEquiv.toLinearMap := by
  have hH := fun operator : S => isotypicLeftAction_adjoint_QECertChecked S component operator
  have hK := fun operator : S => isotypicLeftActionOnCopies_adjoint S W n operator
  let componentTransport : (component.1.restrictScalars Complex) ≃ₗ[S] component.1 :=
    Submodule.restrictScalarsEquiv (S := Complex) (R := S) (M := B) component.1
  let factorTransport : W ≃ₗ[S] W.restrictScalars Complex :=
    (Submodule.restrictScalarsEquiv (S := Complex) (R := S) (M := B) W).symm
  let piFactorTransport : (Fin n → W) ≃ₗ[S] (Fin n → W.restrictScalars Complex) :=
    LinearEquiv.piCongrRight (fun _ => factorTransport)
  let e0 : (component.1.restrictScalars Complex) ≃ₗ[S]
      (Fin n → W.restrictScalars Complex) :=
    componentTransport.trans (e.trans piFactorTransport)
  let rawEquiv : (PiLp 2 (fun _ : Fin n => W.restrictScalars Complex)) ≃ₗ[Complex]
      (Fin n → W.restrictScalars Complex) :=
    (PiLp.continuousLinearEquiv 2 Complex
      (fun _ : Fin n => W.restrictScalars Complex)).toLinearEquiv
  let eHilbert : (component.1.restrictScalars Complex) ≃ₗ[Complex]
      (PiLp 2 (fun _ : Fin n => W.restrictScalars Complex)) :=
    (e0.restrictScalars Complex).trans rawEquiv.symm
  have he_intertwines : ∀ operator : S,
      eHilbert.toLinearMap.comp (isotypicLeftAction S component operator) =
        (isotypicLeftActionOnCopies S W n operator).comp eHilbert.toLinearMap := by
    intro operator
    apply LinearMap.ext
    intro vector
    ext index
    dsimp [eHilbert, rawEquiv, isotypicLeftAction, isotypicLeftActionOnCopies]
    change (e0 (operator • vector) index : B) =
      ((operator : Semantics.Operator B) (e0 vector index : B))
    rw [e0.map_smul]
    rfl
  exact unitary_star_intertwiner_of_linearEquiv
    (isotypicLeftAction S component) (isotypicLeftActionOnCopies S W n) hH hK eHilbert
    he_intertwines
end QEC.Bounds.BPTCommutingProjectorModel
