-- Prove2me | solution 1 for SumProduct.exists_coord_dist_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:52:08.090079+00:00
-- url     : https://prove2.me/submissions/7835befc-7c9b-49c1-8aa9-0c32cd75c17e

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount
import Theorems.Thm_SumProduct_exists_place_ge_one
import Theorems.Thm_SumProduct_abs_realEmbed
import Theorems.Thm_SumProduct_mem_boxMult
attribute [local simp] SumProduct.mem_boxMult



set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open NumberField NumberField.InfinitePlace
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {α β : 𝓞 K} (h : α ≠ β) :
    ∃ w : InfinitePlace K, 1 ≤ |realEmbed K α w - realEmbed K β w| := by
  obtain ⟨w, hw⟩ := exists_place_ge_one (sub_ne_zero.mpr h)
  refine ⟨w, ?_⟩
  have hsub : realEmbed K α w - realEmbed K β w = realEmbed K (α - β) w := by
    simp only [realEmbed]
    rw [show ((α - β : 𝓞 K) : K) = (α : K) - (β : K) by push_cast; ring, map_sub]
  rw [hsub, abs_realEmbed]
  exact hw
end SumProduct
