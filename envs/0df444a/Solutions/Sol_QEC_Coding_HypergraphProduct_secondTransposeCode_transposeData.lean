-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.secondTransposeCode_transposeData
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:34:00.974196+00:00
-- url     : https://prove2.me/submissions/86fc0a20-3bf5-4fa6-af86-daa6f499610a

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Embedding
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Duality

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {F : Type v} {rowOne colOne rowTwo colTwo : Type u}
    [Field F] [Fintype F]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data F rowOne colOne rowTwo colTwo) :
    secondTransposeCode (transposeData D) = secondCode D := by
  rfl
end QEC.Coding.HypergraphProduct
