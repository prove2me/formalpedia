-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorCompressionRight_eq_sequentialSecondCutCompression
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:28:49.092205+00:00
-- url     : https://prove2.me/submissions/95228ce7-e8ee-4ea9-a55d-343f725a8702

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
set_option maxHeartbeats 800000

private theorem compression_comp_embedding_aux
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (E : B →ₗ[Complex] A) (K : C →ₗ[Complex] B) (R : Semantics.Operator A) :
    (LinearMap.adjoint (E.comp K)).comp (R.comp (E.comp K)) =
      (LinearMap.adjoint K).comp
        (((LinearMap.adjoint E).comp (R.comp E)).comp K) := by
  rw [LinearMap.adjoint_comp]
  simp only [LinearMap.comp_assoc]

private theorem compression_congr_of_embedding_eq_aux
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (R : Semantics.Operator A) {J K : B →ₗ[Complex] A} (hJ : J = K) :
    (LinearMap.adjoint J).comp (R.comp J) =
      (LinearMap.adjoint K).comp (R.comp K) := by
  exact congrArg (fun E => (LinearMap.adjoint E).comp (R.comp E)) hJ

private theorem secondCutFactorizedCompression_eq_sequential_aux
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    (LinearMap.adjoint ((M.secondCutSelectedBEmbedding region pB).comp
      (M.secondCutSelectedCAfterBEmbedding region pB pC))).comp
      ((M.secondCutCodeLift region).comp
        ((M.secondCutSelectedBEmbedding region pB).comp
          (M.secondCutSelectedCAfterBEmbedding region pB pC))) =
      M.sequentialSecondCutJointCompression region pB pC := by
  exact compression_comp_embedding_aux
    (M.secondCutSelectedBEmbedding region pB)
    (M.secondCutSelectedCAfterBEmbedding region pB pC)
    (M.secondCutCodeLift region)

theorem solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (pB : Submodule Complex (M.fourFactorB region))
    (pC : Submodule Complex (M.fourFactorC region)) :
    M.secondCutJointCompression region pB pC =
      M.sequentialSecondCutJointCompression region pB pC := by
  have hJ :
      jointBCSectorEmbeddingRight (A := M.fourFactorA region)
        (D := M.fourFactorD region) pB pC =
        (M.secondCutSelectedBEmbedding region pB).comp
          (M.secondCutSelectedCAfterBEmbedding region pB pC) := by
    apply LinearMap.ext
    intro vector
    induction vector using TensorProduct.induction_on with
    | zero => simp
    | tmul ab cd =>
        induction ab using TensorProduct.induction_on with
        | zero => simp
        | tmul a b =>
            induction cd using TensorProduct.induction_on with
            | zero => simp
            | tmul c d => rfl
            | add first second hfirst hsecond =>
                simpa only [TensorProduct.tmul_add, map_add] using
                  congrArg₂ (· + ·) hfirst hsecond
        | add first second hfirst hsecond =>
            simpa only [TensorProduct.add_tmul, map_add] using
              congrArg₂ (· + ·) hfirst hsecond
    | add first second hfirst hsecond =>
        simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond
  unfold secondCutJointCompression
  calc
    (LinearMap.adjoint
      (jointBCSectorEmbeddingRight (A := M.fourFactorA region)
        (D := M.fourFactorD region) pB pC)).comp
      ((M.secondCutCodeLift region).comp
        (jointBCSectorEmbeddingRight (A := M.fourFactorA region)
          (D := M.fourFactorD region) pB pC)) =
      (LinearMap.adjoint ((M.secondCutSelectedBEmbedding region pB).comp
        (M.secondCutSelectedCAfterBEmbedding region pB pC))).comp
        ((M.secondCutCodeLift region).comp
          ((M.secondCutSelectedBEmbedding region pB).comp
            (M.secondCutSelectedCAfterBEmbedding region pB pC))) :=
        compression_congr_of_embedding_eq_aux (M.secondCutCodeLift region) hJ
    _ = _ := secondCutFactorizedCompression_eq_sequential_aux M region pB pC
