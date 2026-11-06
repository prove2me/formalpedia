-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.tensorMap_left_compression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:03:54.742793+00:00
-- url     : https://prove2.me/submissions/6b2dada3-d7e8-4db3-8cae-3524644a096b

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Transport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_BlockTransport

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
    (P : Semantics.Operator A) (Q : Semantics.Operator B) (K : C →ₗ[Complex] A) :
    (LinearMap.adjoint (TensorProduct.map K (1 : Semantics.Operator B))).comp
        ((TensorProduct.map P Q).comp (TensorProduct.map K (1 : Semantics.Operator B))) =
      TensorProduct.map ((LinearMap.adjoint K).comp (P.comp K)) Q := by
  rw [TensorProduct.adjoint_map, LinearMap.adjoint_one]
  rw [← LinearMap.comp_assoc, ← TensorProduct.map_comp]
  rw [← TensorProduct.map_comp]
  rfl
end QEC.Bounds.BPTCommutingProjectorModel
