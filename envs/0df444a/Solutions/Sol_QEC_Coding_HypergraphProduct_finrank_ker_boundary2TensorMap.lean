-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.finrank_ker_boundary2TensorMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:39:40.337388+00:00
-- url     : https://prove2.me/submissions/218ad7ce-7015-4887-8359-cdae8581d753

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Formula

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
    Module.finrank (ZMod 2) (LinearMap.ker (boundary2TensorMap D)) =
      Module.finrank (ZMod 2) (LinearMap.ker (boundary2 D)) := by
  unfold boundary2TensorMap
  rw [LinearEquiv.ker_comp]
  exact LinearEquiv.finrank_eq
    (kerCompLinearEquiv
      (wordTensorEquiv (ZMod 2) colOne rowTwo) (boundary2 D))
end QEC.Coding.HypergraphProduct
