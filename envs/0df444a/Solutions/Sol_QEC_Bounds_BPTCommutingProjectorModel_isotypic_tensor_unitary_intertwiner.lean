-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.isotypic_tensor_unitary_intertwiner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:45:46.552336+00:00
-- url     : https://prove2.me/submissions/4bcad226-d34b-4a34-bc54-42e3c0439f2d

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
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypic_star_unitary_intertwiner
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypic_copy_tensor_unitary_intertwiner
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryTransport_conjOperator_eq_of_intertwines

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
      (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n)),
      ∀ operator : S,
        U.conjOperator (isotypicLeftAction S component operator) =
          isotypicTensorLeftAction S W n operator := by
  rcases isotypic_star_unitary_intertwiner S component n W e with ⟨Ucomponent, hcomponent⟩
  rcases isotypic_copy_tensor_unitary_intertwiner S W n with ⟨Ucopies, hcopies⟩
  let U := composeUnitaryTransport Ucomponent Ucopies
  refine ⟨U, ?_⟩
  intro operator
  apply unitaryTransport_conjOperator_eq_of_intertwines U
  change
    (Ucopies.toLinearEquiv.toLinearMap.comp Ucomponent.toLinearEquiv.toLinearMap).comp
        (isotypicLeftAction S component operator) =
      (isotypicTensorLeftAction S W n operator).comp
        (Ucopies.toLinearEquiv.toLinearMap.comp Ucomponent.toLinearEquiv.toLinearMap)
  calc
    (Ucopies.toLinearEquiv.toLinearMap.comp Ucomponent.toLinearEquiv.toLinearMap).comp
        (isotypicLeftAction S component operator) =
        Ucopies.toLinearEquiv.toLinearMap.comp
          (Ucomponent.toLinearEquiv.toLinearMap.comp
            (isotypicLeftAction S component operator)) := by
          rw [LinearMap.comp_assoc]
    _ = Ucopies.toLinearEquiv.toLinearMap.comp
          ((isotypicLeftActionOnCopies S W n operator).comp
            Ucomponent.toLinearEquiv.toLinearMap) := by
          rw [hcomponent operator]
    _ = (Ucopies.toLinearEquiv.toLinearMap.comp
          (isotypicLeftActionOnCopies S W n operator)).comp
            Ucomponent.toLinearEquiv.toLinearMap := by
          rw [← LinearMap.comp_assoc]
    _ = ((isotypicTensorLeftAction S W n operator).comp
          Ucopies.toLinearEquiv.toLinearMap).comp Ucomponent.toLinearEquiv.toLinearMap := by
          rw [hcopies operator]
    _ = (isotypicTensorLeftAction S W n operator).comp
          (Ucopies.toLinearEquiv.toLinearMap.comp Ucomponent.toLinearEquiv.toLinearMap) := by
      rw [LinearMap.comp_assoc]
end QEC.Bounds.BPTCommutingProjectorModel
