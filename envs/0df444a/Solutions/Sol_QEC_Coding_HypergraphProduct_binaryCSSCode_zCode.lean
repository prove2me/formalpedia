-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.binaryCSSCode_zCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:12:50.755963+00:00
-- url     : https://prove2.me/submissions/67606d7d-3606-4741-b3ba-5e0851c3d94e

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_HypergraphProduct_Core

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
    (binaryCSSCode D).zCode = (chainComplex D).middleBoundaryCode := by
  rfl
end QEC.Coding.HypergraphProduct
