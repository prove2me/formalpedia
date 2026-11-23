-- Prove2me | solution 1 for SumProduct.abs_realEmbed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:54:21.921218+00:00
-- url     : https://prove2.me/submissions/13f76465-0f8b-497a-bae9-e46c659a76dd

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open NumberField NumberField.InfinitePlace
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (α : 𝓞 K) (w : InfinitePlace K) : |realEmbed K α w| = w (α : K) := by
  rw [realEmbed, ← Real.norm_eq_abs, norm_embedding_of_isReal]
end SumProduct
