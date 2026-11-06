-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCutResidualTheta_isSymmetricProjection_of_common_first_second_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:04:56.473329+00:00
-- url     : https://prove2.me/submissions/a120da9d-b63c-4b5a-a196-5fe8cfec6c85

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Tensor
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ResidualProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutResidualTheta_eq_of_common_first_second_block
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_right_factor_isSymmetricProjection_of_tensor_product_projection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_conjOperator_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorSwapUnitary_conj_tensorMap


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
    (eta : D) (heta : ‖eta‖ = 1) (P_D : Semantics.Operator D)
    (hP_D : P_D.IsSymmetricProjection) (hP_D0 : P_D ≠ 0) (hPeta : P_D eta = eta)
    (Qright : Semantics.Operator (Semantics.CompositeSystem N (Semantics.CompositeSystem C D)))
    (Theta : Semantics.Operator (Semantics.CompositeSystem N C))
    (hQright : Qright.IsSymmetricProjection)
    (hcommon : (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
      TensorProduct.map Theta P_D) :
    (secondCutResidualTheta eta Qright).IsSymmetricProjection := by
  have hblock : (TensorProduct.map Theta P_D).IsSymmetricProjection := by
    rw [← hcommon]
    exact (isSymmetricProjection_conjOperator_iff (tensorAssociatorUnitary N C D).symm Qright).mpr
      hQright
  have hswapped : (TensorProduct.map P_D Theta).IsSymmetricProjection := by
    rw [← tensorSwapUnitary_conj_tensorMap]
    exact (isSymmetricProjection_conjOperator_iff
      (tensorSwapUnitary (Semantics.CompositeSystem N C) D) _).mpr hblock
  rw [secondCutResidualTheta_eq_of_common_first_second_block eta heta P_D hPeta Qright Theta hcommon]
  exact right_factor_isSymmetricProjection_of_tensor_product_projection P_D Theta hP_D hP_D0 hswapped
end QEC.Bounds.BPTCommutingProjectorModel
