-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCutResidualTheta_two_sided_scalar_compressions_for_noCloning
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:07:05.270231+00:00
-- url     : https://prove2.me/submissions/76e256f2-3641-4086-984e-490522aeb598

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ResidualProjection
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_ResidualScalar
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutResidualTheta_scalar_compression_of_common_first_second_block

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
    (Theta : Semantics.Operator (Semantics.CompositeSystem N C))
    (hcommon : (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
      TensorProduct.map Theta P_D)
    (hinternal : ∀ X : Semantics.Operator N, ∃ scalar : Complex,
      (tensorAssociatorUnitary N C D).symm.conjOperator Qright *
          TensorProduct.map (TensorProduct.map X (1 : Semantics.Operator C))
            (1 : Semantics.Operator D) *
          (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
        scalar • (tensorAssociatorUnitary N C D).symm.conjOperator Qright)
    (hexternal : ∀ Y : Semantics.Operator C, ∃ scalar : Complex,
      (tensorAssociatorUnitary N C D).symm.conjOperator Qright *
          TensorProduct.map (TensorProduct.map (1 : Semantics.Operator N) Y)
            (1 : Semantics.Operator D) *
          (tensorAssociatorUnitary N C D).symm.conjOperator Qright =
        scalar • (tensorAssociatorUnitary N C D).symm.conjOperator Qright) :
    (∀ X : Semantics.Operator N, ∃ scalar : Complex,
      Theta * TensorProduct.map X (1 : Semantics.Operator C) * Theta = scalar • Theta) ∧
    (∀ Y : Semantics.Operator C, ∃ scalar : Complex,
      Theta * TensorProduct.map (1 : Semantics.Operator N) Y * Theta = scalar • Theta) := by
  constructor
  · intro X
    exact secondCutResidualTheta_scalar_compression_of_common_first_second_block
      eta heta P_D hP_D hPeta Qright Theta (TensorProduct.map X (1 : Semantics.Operator C))
        hcommon (hinternal X)
  · intro Y
    exact secondCutResidualTheta_scalar_compression_of_common_first_second_block
      eta heta P_D hP_D hPeta Qright Theta (TensorProduct.map (1 : Semantics.Operator N) Y)
        hcommon (hexternal Y)
end QEC.Bounds.BPTCommutingProjectorModel
