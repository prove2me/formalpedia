-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.leftTensorCompression_tensorMap_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:12:33.161866+00:00
-- url     : https://prove2.me/submissions/57092d7b-b592-4613-a551-f87d74325300

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
    (T : Semantics.Operator B) (eta : A) (heta : ‖eta‖ = 1) :
    leftTensorCompression eta (TensorProduct.map (1 : Semantics.Operator A) T) = T := by
  apply LinearMap.ext
  intro b
  change LinearMap.adjoint (overlapLeftEmbedding A B eta)
      ((TensorProduct.map (1 : Semantics.Operator A) T)
        (overlapLeftEmbedding A B eta b)) = T b
  change LinearMap.adjoint (overlapLeftEmbedding A B eta) (eta ⊗ₜ[Complex] T b) = T b
  rw [adjoint_overlapLeftEmbedding_apply_tmul]
  rw [inner_self_eq_norm_sq_to_K, heta]
  norm_num
end QEC.Bounds.BPTCommutingProjectorModel
