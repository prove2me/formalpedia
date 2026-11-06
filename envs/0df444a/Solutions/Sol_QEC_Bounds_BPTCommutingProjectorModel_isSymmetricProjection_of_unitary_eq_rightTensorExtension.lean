-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_of_unitary_eq_rightTensorExtension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:59:20.12854+00:00
-- url     : https://prove2.me/submissions/3dbde797-3ee5-458d-9f7c-417a42f033fd

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Embedding
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_of_tensorMap_left_one
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_congr
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_conjOperator_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_of_rightTensorExtensionAfterLeft


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
    {A H W N : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (P : Semantics.Operator (Semantics.CompositeSystem A H))
    (Pleft : Semantics.Operator (Semantics.CompositeSystem A W))
    (eta : N) (heta : ‖eta‖ = 1)
    (hP : P.IsSymmetricProjection)
    (hleft : (unitaryLTensor A U).conjOperator P =
      rightTensorExtensionAfterLeft A W N Pleft) :
    Pleft.IsSymmetricProjection := by
  have htransported : (rightTensorExtensionAfterLeft A W N Pleft).IsSymmetricProjection :=
    isSymmetricProjection_congr
      ((isSymmetricProjection_conjOperator_iff (unitaryLTensor A U) P).mpr hP) hleft
  have hmap : (TensorProduct.map Pleft (1 : Semantics.Operator N)).IsSymmetricProjection :=
    isSymmetricProjection_of_rightTensorExtensionAfterLeft Pleft htransported
  exact isSymmetricProjection_of_tensorMap_left_one Pleft eta heta hmap
end QEC.Bounds.BPTCommutingProjectorModel
