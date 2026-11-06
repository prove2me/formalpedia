-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.binaryCSSCode_stabilizer_isSourceValidBinary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:27:40.675068+00:00
-- url     : https://prove2.me/submissions/66f8cf46-4b4a-4d3d-8102-e7f42f22e7c3

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
    (binaryCSSCode D).stabilizer.IsSourceValidBinary := by
  exact (chainComplex D).binaryCSSCode_stabilizer_isSourceValidBinary
end QEC.Coding.HypergraphProduct
