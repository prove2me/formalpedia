-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.commute_leftOverlap_of_commute_leftInteractionCoefficients
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:40:39.960221+00:00
-- url     : https://prove2.me/submissions/ce638101-27d4-4f69-ac22-addd2c1233ad

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
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_operator_eq_of_leftInteractionCoefficients_eq
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_leftInteractionCoefficient_mul_rightTensor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_leftInteractionCoefficient_leftTensor_mul

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
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B)) (Z : Semantics.Operator B)
    (hcommute : ∀ a a' : A, Commute Z (leftInteractionCoefficient P a a')) :
    Commute P (TensorProduct.map (1 : Semantics.Operator A) Z) := by
  change P * TensorProduct.map (1 : Semantics.Operator A) Z =
    TensorProduct.map (1 : Semantics.Operator A) Z * P
  apply operator_eq_of_leftInteractionCoefficients_eq
  intro a a'
  rw [leftInteractionCoefficient_mul_rightTensor,
    leftInteractionCoefficient_leftTensor_mul]
  exact (hcommute a a').eq.symm
end QEC.Bounds.BPTCommutingProjectorModel
