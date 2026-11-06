-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.commute_rightOverlap_of_commute_rightInteractionCoefficients
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:41:01.830137+00:00
-- url     : https://prove2.me/submissions/c7469dda-c8ca-4f8b-8e2b-7206cf8380ed

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
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_operator_eq_of_rightInteractionCoefficients_eq
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_rightInteractionCoefficient_leftTensor_mul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_rightInteractionCoefficient_mul_leftTensor

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
    {B C : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (Q : Semantics.Operator (Semantics.CompositeSystem B C)) (Z : Semantics.Operator B)
    (hcommute : ∀ c c' : C, Commute Z (rightInteractionCoefficient Q c c')) :
    Commute Q (TensorProduct.map Z (1 : Semantics.Operator C)) := by
  change Q * TensorProduct.map Z (1 : Semantics.Operator C) =
    TensorProduct.map Z (1 : Semantics.Operator C) * Q
  apply operator_eq_of_rightInteractionCoefficients_eq
  intro c c'
  rw [rightInteractionCoefficient_mul_leftTensor,
    rightInteractionCoefficient_leftTensor_mul]
  exact (hcommute c c').eq.symm
end QEC.Bounds.BPTCommutingProjectorModel
