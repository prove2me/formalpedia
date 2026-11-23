-- Prove2me | solution 1 for SumProduct.latticeEquiv_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:49:34.610625+00:00
-- url     : https://prove2.me/submissions/b8b45f40-0c8d-41b5-9222-86d229cf0056

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open NumberField.mixedEmbedding
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] (α : 𝓞 K) :
    ((latticeEquiv K α : mixedSpace K)) = latticeEmbed K α := rfl
end SumProduct
