-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.leftIsotypicSectorProjector_commutes_overlap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:43:14.977844+00:00
-- url     : https://prove2.me/submissions/13929139-4d88-4b6a-b368-867cc44c8d29

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
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_commute_leftOverlap_of_commute_leftInteractionCoefficients
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_commute_rightOverlap_of_commute_rightInteractionCoefficients
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_leftIsotypicSectorProjector_commute_leftInteractionCoefficient
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_leftIsotypicSectorProjector_commute_rightInteractionCoefficient

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
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    Commute P (TensorProduct.map (1 : Semantics.Operator A)
      (leftIsotypicSectorProjector P component)) ∧
    Commute Q (TensorProduct.map (leftIsotypicSectorProjector P component)
      (1 : Semantics.Operator C)) := by
  constructor
  · apply commute_leftOverlap_of_commute_leftInteractionCoefficients
    intro a a'
    exact leftIsotypicSectorProjector_commute_leftInteractionCoefficient
      P component a a'
  · apply commute_rightOverlap_of_commute_rightInteractionCoefficients
    intro c c'
    exact leftIsotypicSectorProjector_commute_rightInteractionCoefficient
      P Q hselfAdjoint hcommute component c c'
end QEC.Bounds.BPTCommutingProjectorModel
