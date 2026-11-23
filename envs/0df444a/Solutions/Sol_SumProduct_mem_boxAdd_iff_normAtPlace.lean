-- Prove2me | solution 1 for SumProduct.mem_boxAdd_iff_normAtPlace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:05:20.681397+00:00
-- url     : https://prove2.me/submissions/83bdffce-9d8b-404f-b228-5106073f1290

import Mathlib
import Definitions.Def_SumProduct_Boxes

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {X : ℝ} {α : 𝓞 K} :
    α ∈ boxAdd K X ↔ ∀ w : InfinitePlace K, normAtPlace w (mixedEmbedding K (α : K)) ≤ X := by
  rw [mem_boxAdd]; simp only [normAtPlace_apply]
end SumProduct
