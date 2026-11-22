-- Prove2me | solution 1 for SumProduct.mem_boxMult
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:47:31.255314+00:00
-- url     : https://prove2.me/submissions/b87fb2bc-aa7b-47b0-9c90-1d244f5c67d2

import Mathlib
import Definitions.Def_SumProduct_Boxes

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {Y : ℝ} {u : (𝓞 K)ˣ} :
    u ∈ boxMult K Y ↔ ∀ w : NumberField.InfinitePlace K, |Real.log (w ((u : 𝓞 K) : K))| ≤ Y :=
  Set.Finite.mem_toFinset _
end SumProduct
