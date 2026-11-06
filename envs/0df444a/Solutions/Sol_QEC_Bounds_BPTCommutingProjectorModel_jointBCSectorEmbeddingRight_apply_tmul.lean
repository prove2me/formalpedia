-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingRight_apply_tmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:25:10.867955+00:00
-- url     : https://prove2.me/submissions/a77a7fcc-8e89-409a-b233-681ae7a2e3fa

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Core
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector

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
    (a : A) (b : pB) (c : pC) (d : D) :
    jointBCSectorEmbeddingRight pB pC ((a ⊗ₜ[Complex] b) ⊗ₜ[Complex] (c ⊗ₜ[Complex] d)) =
      (a ⊗ₜ[Complex] b.1) ⊗ₜ[Complex] (c.1 ⊗ₜ[Complex] d) := by
  rfl
end QEC.Bounds.BPTCommutingProjectorModel
