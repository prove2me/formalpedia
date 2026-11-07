-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.finrank_ker_boundary2_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:47:04.169771+00:00
-- url     : https://prove2.me/submissions/0506ba89-d4b4-43dc-bc70-be6dfaacea01

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Formula
import Theorems.Thm_QEC_Coding_HypergraphProduct_ker_jointTensorWordMap_eq
import Theorems.Thm_QEC_Coding_HypergraphProduct_finrank_ker_boundary2TensorMap
import Theorems.Thm_QEC_Coding_HypergraphProduct_boundary2TensorMap_eq_joint
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
    Module.finrank (ZMod 2) (LinearMap.ker (boundary2 D)) =
      Dimension (firstCode D) * Dimension (secondTransposeCode D) := by
  calc
    _ = Module.finrank (ZMod 2)
          (LinearMap.ker (boundary2TensorMap D)) :=
      (finrank_ker_boundary2TensorMap D).symm
    _ = Module.finrank (ZMod 2)
          (LinearMap.ker
            (jointTensorWordMap (Matrix.toLin' D.first)
              (Matrix.toLin' D.second.transpose))) := by
      rw [boundary2TensorMap_eq_joint]
    _ = Module.finrank (ZMod 2)
          (LinearMap.ker
            (jointTensorMap (Matrix.toLin' D.first)
              (Matrix.toLin' D.second.transpose))) := by
      rw [ker_jointTensorWordMap_eq]
    _ = Module.finrank (ZMod 2)
          (LinearMap.ker (Matrix.toLin' D.first)) *
        Module.finrank (ZMod 2)
          (LinearMap.ker (Matrix.toLin' D.second.transpose)) :=
      finrank_ker_jointTensorMap _ _
    _ = Dimension (firstCode D) * Dimension (secondTransposeCode D) := by
      rfl
end QEC.Coding.HypergraphProduct
