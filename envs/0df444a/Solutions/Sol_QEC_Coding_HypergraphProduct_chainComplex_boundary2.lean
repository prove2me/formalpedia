-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.chainComplex_boundary2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:12:34.203207+00:00
-- url     : https://prove2.me/submissions/fe0e32a6-3f6d-441a-b0a2-25efebc3242c

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_HypergraphProduct_Core

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {F : Type u} {rowOne colOne rowTwo colTwo : Type v}
    [Field F] [Fintype F]
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) :
    (chainComplex D).boundary2 = boundary2 D := by
  rfl
end QEC.Coding.HypergraphProduct
