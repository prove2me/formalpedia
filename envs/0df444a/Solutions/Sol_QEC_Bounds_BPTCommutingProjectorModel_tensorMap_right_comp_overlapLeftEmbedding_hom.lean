-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.tensorMap_right_comp_overlapLeftEmbedding_hom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:24:15.643626+00:00
-- url     : https://prove2.me/submissions/e1160563-c2dc-4bcc-a7f0-c7169ad59151

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
    (a : A) (Z : B →ₗ[Complex] C) :
    (TensorProduct.map (1 : Semantics.Operator A) Z).comp
      (overlapLeftEmbedding A B a) =
        (overlapLeftEmbedding A C a).comp Z := by
  apply LinearMap.ext
  intro vector
  rfl
end QEC.Bounds.BPTCommutingProjectorModel
