-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryTaggedEncodingIsometry_eq_tensorCube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:29:57.094295+00:00
-- url     : https://prove2.me/submissions/f8762234-83d4-47a0-9195-f75a7cdee87f

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTaggedEncoding
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_TensorRegister
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTensorEncoding
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryTaggedEncodingIsometry_basis_apply_product
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedExtension_trans
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_taggedTensorCube_basis_apply


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS Ngu24MultiplicativeCCZ
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution (i : Nat)
    (psi : TaggedThreeCopyRegister (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) :
    binaryTaggedEncodingIsometry i psi =
      taggedTensorCube (ZMod 2) (Fin (f256MultiplicationLogicalCount i))
        ((f256SourceInput i).PivotComplement × Fin 512) (binaryEncodingIsometry i).toLinearMap psi := by
  let B := EuclideanSpace.basisFun
    (TaggedThreeCopyRegisterLabel (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) Complex
  change binaryTaggedEncodingLinearMap i psi = _
  rw [← B.sum_repr psi]
  erw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro u _
  erw [map_smul, map_smul]
  congr 1
  ext v
  exact (binaryTaggedEncodingIsometry_basis_apply_product i u v).trans
    (taggedTensorCube_basis_apply (ZMod 2) (Fin (f256MultiplicationLogicalCount i))
      ((f256SourceInput i).PivotComplement × Fin 512) (binaryEncodingIsometry i).toLinearMap u v).symm
end QEC.Distillation.Ngu24Binary
