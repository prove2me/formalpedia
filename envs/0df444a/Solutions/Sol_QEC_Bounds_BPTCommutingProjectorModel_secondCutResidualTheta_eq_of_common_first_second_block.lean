-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCutResidualTheta_eq_of_common_first_second_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:09:20.333236+00:00
-- url     : https://prove2.me/submissions/fd81d2f1-d929-45bd-968c-3b17be55a5a8

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Tensor
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ResidualProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_rightTensorCompression_tensorMap


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
    {N C D : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (eta : D) (heta : ‖eta‖ = 1) (P_D : Semantics.Operator D) (hPeta : P_D eta = eta)
    (Qright : Semantics.Operator (Semantics.CompositeSystem N (Semantics.CompositeSystem C D)))
    (Theta : Semantics.Operator (Semantics.CompositeSystem N C))
    (hcommon : (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
      TensorProduct.map Theta P_D) :
    secondCutResidualTheta eta Qright = Theta := by
  unfold secondCutResidualTheta
  rw [hcommon, rightTensorCompression_tensorMap, hPeta, inner_self_eq_norm_sq_to_K, heta]
  norm_num
end QEC.Bounds.BPTCommutingProjectorModel
