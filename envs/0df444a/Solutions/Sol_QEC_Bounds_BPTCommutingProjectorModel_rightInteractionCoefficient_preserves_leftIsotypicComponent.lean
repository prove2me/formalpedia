-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.rightInteractionCoefficient_preserves_leftIsotypicComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:01:32.832626+00:00
-- url     : https://prove2.me/submissions/a3471556-b721-44ea-9622-90cead411015

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
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (W : Submodule (leftInteractionAlgebra P) B) [IsSimpleModule (leftInteractionAlgebra P) W]
    (c c' : C) {vector : B}
    (hvector : vector ∈ isotypicComponent (leftInteractionAlgebra P) B W) :
    rightInteractionCoefficient Q c c' vector ∈
      isotypicComponent (leftInteractionAlgebra P) B W := by
  let rightCoefficient := rightInteractionCoefficient Q c c'
  let rightEnd : Module.End (leftInteractionAlgebra P) B :=
    commutingOperatorAsModuleEnd (leftInteractionAlgebra P) rightCoefficient (by
      intro operator
      exact interactionAlgebras_commute P Q hselfAdjoint hcommute operator.property
        (by
          apply StarAlgebra.subset_adjoin
          exact ⟨c, c', rfl⟩))
  have hfullyInvariant : (isotypicComponent (leftInteractionAlgebra P) B W).IsFullyInvariant :=
    Submodule.IsFullyInvariant.isotypicComponent (leftInteractionAlgebra P) B W
  change rightEnd vector ∈ isotypicComponent (leftInteractionAlgebra P) B W
  exact hfullyInvariant rightEnd hvector
end QEC.Bounds.BPTCommutingProjectorModel
