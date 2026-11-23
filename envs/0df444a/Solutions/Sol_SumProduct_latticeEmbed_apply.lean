-- Prove2me | solution 1 for SumProduct.latticeEmbed_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:49:12.519766+00:00
-- url     : https://prove2.me/submissions/c58fa224-cb40-45c4-ba29-ded51bcfeca6

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] (α : 𝓞 K) :
    latticeEmbed K α = NumberField.mixedEmbedding K (algebraMap (𝓞 K) K α) := rfl
end SumProduct
