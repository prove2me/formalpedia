-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.rightTensorCompression_tensorMap_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:03:26.364256+00:00
-- url     : https://prove2.me/submissions/aed08653-a143-4821-8ea9-1b8c02f1f86d

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
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (T : Semantics.Operator A) (eta : B) (heta : ‖eta‖ = 1) :
    rightTensorCompression eta (TensorProduct.map T (1 : Semantics.Operator B)) = T := by
  apply LinearMap.ext
  intro a
  change LinearMap.adjoint (overlapRightEmbedding A B eta)
      ((TensorProduct.map T (1 : Semantics.Operator B))
        (overlapRightEmbedding A B eta a)) = T a
  change LinearMap.adjoint (overlapRightEmbedding A B eta) (T a ⊗ₜ[Complex] eta) = T a
  rw [adjoint_overlapRightEmbedding_apply_tmul]
  rw [inner_self_eq_norm_sq_to_K, heta]
  norm_num
end QEC.Bounds.BPTCommutingProjectorModel
