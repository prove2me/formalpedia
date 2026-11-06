-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.tensorMap_right_compression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:03:53.827099+00:00
-- url     : https://prove2.me/submissions/5be50dd3-7e90-40bc-8851-4983ab2d4aeb

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
    (P : Semantics.Operator A) (Q : Semantics.Operator B) (K : C →ₗ[Complex] B) :
    (LinearMap.adjoint (TensorProduct.map (1 : Semantics.Operator A) K)).comp
        ((TensorProduct.map P Q).comp (TensorProduct.map (1 : Semantics.Operator A) K)) =
      TensorProduct.map P ((LinearMap.adjoint K).comp (Q.comp K)) := by
  rw [TensorProduct.adjoint_map, LinearMap.adjoint_one]
  rw [← LinearMap.comp_assoc, ← TensorProduct.map_comp]
  rw [← TensorProduct.map_comp]
  rfl
end QEC.Bounds.BPTCommutingProjectorModel
