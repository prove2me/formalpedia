-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.productBlockRegrouping_apply_tmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:26:38.0546+00:00
-- url     : https://prove2.me/submissions/ef2c056c-5240-4368-857c-2bb581e5c24a

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Regrouping

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
    {A W N X D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (a : A) (w : W) (n : N) (x : X) (d : D) :
    productBlockRegrouping
      (((a ⊗ₜ[Complex] w) ⊗ₜ[Complex] (n ⊗ₜ[Complex] x)) ⊗ₜ[Complex] d) =
      ((a ⊗ₜ[Complex] w) ⊗ₜ[Complex] n) ⊗ₜ[Complex] (x ⊗ₜ[Complex] d) := by
  rfl
end QEC.Bounds.BPTCommutingProjectorModel
