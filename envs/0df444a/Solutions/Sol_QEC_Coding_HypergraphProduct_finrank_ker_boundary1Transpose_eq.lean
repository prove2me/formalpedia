-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.finrank_ker_boundary1Transpose_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:47:00.499206+00:00
-- url     : https://prove2.me/submissions/4118f3dd-6b12-412e-b13a-554fd35a5cd9

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Formula
import Theorems.Thm_QEC_Coding_HypergraphProduct_ker_jointTensorWordMap_eq
import Theorems.Thm_QEC_Coding_HypergraphProduct_finrank_ker_boundary1TransposeTensorMap
import Theorems.Thm_QEC_Coding_HypergraphProduct_boundary1TransposeTensorMap_eq_joint
import Theorems.Thm_QEC_Coding_HypergraphProduct_finrank_ker_jointTensorMap


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    Module.finrank (ZMod 2)
        (LinearMap.ker (wordLinearMapTranspose (boundary1 D))) =
      Dimension (firstTransposeCode D) * Dimension (secondCode D) := by
  calc
    _ = Module.finrank (ZMod 2)
          (LinearMap.ker (boundary1TransposeTensorMap D)) :=
      (finrank_ker_boundary1TransposeTensorMap D).symm
    _ = Module.finrank (ZMod 2)
          (LinearMap.ker
            (jointTensorWordMap (Matrix.toLin' D.first.transpose)
              (Matrix.toLin' D.second))) := by
      rw [boundary1TransposeTensorMap_eq_joint]
    _ = Module.finrank (ZMod 2)
          (LinearMap.ker
            (jointTensorMap (Matrix.toLin' D.first.transpose)
              (Matrix.toLin' D.second))) := by
      rw [ker_jointTensorWordMap_eq]
    _ = Module.finrank (ZMod 2)
          (LinearMap.ker (Matrix.toLin' D.first.transpose)) *
        Module.finrank (ZMod 2)
          (LinearMap.ker (Matrix.toLin' D.second)) :=
      finrank_ker_jointTensorMap _ _
    _ = Dimension (firstTransposeCode D) * Dimension (secondCode D) := by
      rfl
end QEC.Coding.HypergraphProduct
