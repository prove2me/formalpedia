-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCutResidualTheta_scalar_compression_of_common_first_second_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:25:45.108059+00:00
-- url     : https://prove2.me/submissions/9d425000-08ce-4273-b403-3c3c2680e3bb

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ResidualProjection
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ResidualScalar
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_rightTensorCompression_smul
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
    (eta : D) (heta : ‖eta‖ = 1) (P_D : Semantics.Operator D)
    (hP_D : P_D.IsSymmetricProjection) (hPeta : P_D eta = eta)
    (Qright : Semantics.Operator (Semantics.CompositeSystem N (Semantics.CompositeSystem C D)))
    (Theta Z : Semantics.Operator (Semantics.CompositeSystem N C))
    (hcommon : (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
      TensorProduct.map Theta P_D)
    (hscalar : ∃ scalar : Complex,
      (tensorAssociatorUnitary N C D).symm.conjOperator Qright *
          TensorProduct.map Z (1 : Semantics.Operator D) *
          (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
        scalar • (tensorAssociatorUnitary N C D).symm.conjOperator Qright) :
    ∃ scalar : Complex, Theta * Z * Theta = scalar • Theta := by
  rcases hscalar with ⟨scalar, hscalar⟩
  have hinner : inner Complex eta (P_D eta) = 1 := by
    rw [hPeta, inner_self_eq_norm_sq_to_K, heta]
    norm_num
  have hcompress (T : Semantics.Operator (Semantics.CompositeSystem N C)) :
      rightTensorCompression eta (TensorProduct.map T P_D) = T := by
    rw [rightTensorCompression_tensorMap, hinner, one_smul]
  have hmap : TensorProduct.map (Theta * Z * Theta) P_D =
      TensorProduct.map Theta P_D * TensorProduct.map Z (1 : Semantics.Operator D) *
        TensorProduct.map Theta P_D := by
    symm
    calc
      TensorProduct.map Theta P_D * TensorProduct.map Z (1 : Semantics.Operator D) *
          TensorProduct.map Theta P_D =
          TensorProduct.map (Theta * Z) (P_D * (1 : Semantics.Operator D)) *
            TensorProduct.map Theta P_D := by rw [← TensorProduct.map_mul]
      _ = TensorProduct.map ((Theta * Z) * Theta)
          ((P_D * (1 : Semantics.Operator D)) * P_D) := by rw [← TensorProduct.map_mul]
      _ = TensorProduct.map (Theta * Z * Theta) P_D := by
        rw [mul_one, hP_D.isIdempotentElem]
  refine ⟨scalar, ?_⟩
  calc
    Theta * Z * Theta = rightTensorCompression eta (TensorProduct.map (Theta * Z * Theta) P_D) :=
      (hcompress _).symm
    _ = rightTensorCompression eta
        (TensorProduct.map Theta P_D * TensorProduct.map Z (1 : Semantics.Operator D) *
          TensorProduct.map Theta P_D) := congrArg (rightTensorCompression eta) hmap
    _ = rightTensorCompression eta
        ((tensorAssociatorUnitary N C D).symm.conjOperator Qright *
          TensorProduct.map Z (1 : Semantics.Operator D) *
          (tensorAssociatorUnitary N C D).symm.conjOperator Qright) := by rw [← hcommon]
    _ = rightTensorCompression eta
        (scalar • (tensorAssociatorUnitary N C D).symm.conjOperator Qright) :=
      congrArg (rightTensorCompression eta) hscalar
    _ = scalar • rightTensorCompression eta
        ((tensorAssociatorUnitary N C D).symm.conjOperator Qright) :=
      rightTensorCompression_smul eta scalar _
    _ = scalar • Theta := by
      rw [hcommon, rightTensorCompression_tensorMap, hinner, one_smul]
end QEC.Bounds.BPTCommutingProjectorModel
