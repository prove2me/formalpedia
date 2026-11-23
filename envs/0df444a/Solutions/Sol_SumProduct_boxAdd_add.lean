-- Prove2me | solution 1 for SumProduct.boxAdd_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:48:42.061713+00:00
-- url     : https://prove2.me/submissions/c35b28e3-39dc-4e6c-a79d-5cb478bb0f89

import Mathlib
import Definitions.Def_SumProduct_Boxes

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {X Y : ℝ} {α β : 𝓞 K}
    (ha : α ∈ boxAdd K X) (hb : β ∈ boxAdd K Y) : α + β ∈ boxAdd K (X + Y) := by
  rw [mem_boxAdd] at ha hb ⊢
  intro w
  have he : ((α + β : 𝓞 K) : K) = (α : K) + (β : K) := by push_cast; ring
  rw [he]
  exact le_trans (w.1.add_le _ _) (add_le_add (ha w) (hb w))
end SumProduct
