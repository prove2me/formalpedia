-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.compression_eq_sequential_of_eq_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:05:36.948987+00:00
-- url     : https://prove2.me/submissions/993e13b3-3b21-4d6f-bf63-f12b9c683a00

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_ResidualProjection
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_SelectedB
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_SequentialEmbeddingCore
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_compression_comp_embedding

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
    (J : C →ₗ[Complex] A) (E : B →ₗ[Complex] A) (K : C →ₗ[Complex] B)
    (R : Semantics.Operator A) (hJ : J = E.comp K) :
    (LinearMap.adjoint J).comp (R.comp J) =
      (LinearMap.adjoint K).comp
        (((LinearMap.adjoint E).comp (R.comp E)).comp K) := by
  subst J
  exact compression_comp_embedding E K R
end QEC.Bounds.BPTCommutingProjectorModel
