-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fourFactorJointBCSectorEmbedding_apply_factor_through_middle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:36:07.885725+00:00
-- url     : https://prove2.me/submissions/29e97ce5-9371-4538-a202-cc1f673d4ad3

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Core
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorJointBCSectorEmbedding_factor_through_middle

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
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (x : Semantics.CompositeSystem (Semantics.CompositeSystem A pB)
      (Semantics.CompositeSystem pC D)) :
    fourFactorJointBCSectorEmbedding pB pC x =
      (unitaryLTensor A (tensorAssociatorUnitary B C D).symm).symm
        (jointBCSectorMiddleEmbedding pB pC (jointBCSectorMiddleTransport pB pC x)) := by
  exact congrArg (fun f => f x)
    (fourFactorJointBCSectorEmbedding_factor_through_middle
      (A := A) (B := B) (C := C) (D := D) pB pC)
end QEC.Bounds.BPTCommutingProjectorModel
