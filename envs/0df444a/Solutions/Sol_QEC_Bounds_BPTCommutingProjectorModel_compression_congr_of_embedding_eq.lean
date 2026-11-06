-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.compression_congr_of_embedding_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:46:58.838612+00:00
-- url     : https://prove2.me/submissions/b464ddcb-5cd6-4ee9-9776-2abf08bb679c

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_ResidualProjection
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_SelectedB
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_SequentialEmbeddingCore

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
    (R : Semantics.Operator A) {J K : B →ₗ[Complex] A} (hJ : J = K) :
    (LinearMap.adjoint J).comp (R.comp J) =
      (LinearMap.adjoint K).comp (R.comp K) := by
  exact congrArg (fun E => (LinearMap.adjoint E).comp (R.comp E)) hJ
end QEC.Bounds.BPTCommutingProjectorModel
