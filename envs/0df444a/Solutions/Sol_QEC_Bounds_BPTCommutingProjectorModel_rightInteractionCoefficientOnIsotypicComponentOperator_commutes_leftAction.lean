-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.rightInteractionCoefficientOnIsotypicComponentOperator_commutes_leftAction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:43:38.209554+00:00
-- url     : https://prove2.me/submissions/e67f9305-ad48-41f0-9cdd-97cec2420b00

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
    (component : isotypicComponents (leftInteractionAlgebra P) B) (c c' : C)
    (operator : leftInteractionAlgebra P) :
    Commute
      (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
        component c c')
      (isotypicLeftAction (leftInteractionAlgebra P) component operator) := by
  let right := rightInteractionCoefficientOnIsotypicComponent P Q hselfAdjoint hcommute
    component c c'
  change
    (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
      component c c').comp (isotypicLeftAction (leftInteractionAlgebra P) component operator) =
    (isotypicLeftAction (leftInteractionAlgebra P) component operator).comp
      (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
        component c c')
  apply LinearMap.ext
  intro vector
  change right (operator • vector) = operator • right vector
  exact right.map_smul operator vector
end QEC.Bounds.BPTCommutingProjectorModel
