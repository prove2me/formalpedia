-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.commuting_overlap_tensor_block_coefficient_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:55:27.51034+00:00
-- url     : https://prove2.me/submissions/1239168d-6c95-4da8-bb1e-ba1cc3b6790d

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
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_overlap_projector_tensor_block_coefficient_factorization
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_commuting_overlap_block_factorization

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
          (e : component.1 ≃ₗ[leftInteractionAlgebra P] (Fin n → W))
          (U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
            (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n))),
          (∀ a a' : A,
            U.conjOperator
              (isotypicLeftAction (leftInteractionAlgebra P) component
                ⟨leftInteractionCoefficient P a a',
                  leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩) =
              isotypicTensorLeftAction (leftInteractionAlgebra P) W n
                ⟨leftInteractionCoefficient P a a',
                  leftInteractionCoefficient_mem_leftInteractionAlgebra P a a'⟩) ∧
          (∀ c c' : C, ∃ R : Semantics.Operator (EuclideanSpace Complex (Fin n)),
            U.conjOperator
              (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
                component c c') =
              TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex)) R) := by
  rcases commuting_overlap_block_factorization P Q hselfAdjoint hcommute with
    ⟨hInternal, hblocks⟩
  refine ⟨hInternal, ?_⟩
  intro component
  rcases hblocks component with ⟨n, hn, W, hW, e, _, _⟩
  rcases overlap_projector_tensor_block_coefficient_factorization P Q hselfAdjoint hcommute
    component n W hW e with ⟨U, hleft, hright⟩
  exact ⟨n, hn, W, hW, e, U, hleft, hright⟩
end QEC.Bounds.BPTCommutingProjectorModel
