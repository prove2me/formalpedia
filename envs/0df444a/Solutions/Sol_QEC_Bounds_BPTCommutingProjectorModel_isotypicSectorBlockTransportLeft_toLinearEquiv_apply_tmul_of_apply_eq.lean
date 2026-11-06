-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_toLinearEquiv_apply_tmul_of_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:26:50.032881+00:00
-- url     : https://prove2.me/submissions/c8e67d98-fcf0-48bd-829c-c8c362619a04

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Transport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_Coherence
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicSectorBlockTransportLeft_apply_tmul_of_apply_eq

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
    {A H W N C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (a : A) (h : H) (c : C) (w : W) (n : N)
    (hU : U.toLinearEquiv h = w ⊗ₜ[Complex] n) :
    (isotypicSectorBlockTransportLeft A H W N C U).toLinearEquiv
        ((a ⊗ₜ[Complex] h) ⊗ₜ[Complex] c) =
      (a ⊗ₜ[Complex] w) ⊗ₜ[Complex] (n ⊗ₜ[Complex] c) := by
  exact isotypicSectorBlockTransportLeft_apply_tmul_of_apply_eq U a h c w n hU
end QEC.Bounds.BPTCommutingProjectorModel
