-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.finrank_ker_boundary1TransposeTensorMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:39:07.593201+00:00
-- url     : https://prove2.me/submissions/23d9f888-e016-4006-8dcd-60ee226f0244

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
    Module.finrank (ZMod 2) (LinearMap.ker (boundary1TransposeTensorMap D)) =
      Module.finrank (ZMod 2)
        (LinearMap.ker (wordLinearMapTranspose (boundary1 D))) := by
  unfold boundary1TransposeTensorMap
  rw [LinearEquiv.ker_comp]
  exact LinearEquiv.finrank_eq
    (kerCompLinearEquiv
      (wordTensorEquiv (ZMod 2) rowOne colTwo)
      (wordLinearMapTranspose (boundary1 D)))
end QEC.Coding.HypergraphProduct
