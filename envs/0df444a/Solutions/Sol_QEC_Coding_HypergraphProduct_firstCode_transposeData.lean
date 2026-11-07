-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.firstCode_transposeData
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:33:19.040492+00:00
-- url     : https://prove2.me/submissions/7f6af0ab-6670-473b-b8af-ce62c87bad21

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
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    (D : Data F rowOne colOne rowTwo colTwo) :
    firstCode (transposeData D) = firstTransposeCode D := rfl
end QEC.Coding.HypergraphProduct
