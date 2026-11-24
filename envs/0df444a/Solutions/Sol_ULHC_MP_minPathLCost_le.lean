-- Prove2me | solution 1 for ULHC.MP.minPathLCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:22:57.581211+00:00
-- url     : https://prove2.me/submissions/b962834f-da1e-4ab8-b128-74e090ea6eb2

import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_CostMinPath
import Theorems.Thm_ULHC_MP_length_layer
import Theorems.Thm_ULHC_MP_sum_map_le
import Theorems.Thm_ULHC_MP_layerCost_le

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type} [DecidableEq α]
variable (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
  (ec : α → α → ℕ) (sc : α → ℕ) {E S : ℕ}
  (hE : ∀ x ∈ NL, ∀ y ∈ NL, ec x y ≤ E) (hS : ∀ x ∈ NL, sc x ≤ S)
include hE hS
namespace ULHC.MP
theorem _root_.solution : minPathLCost NL mid tgt edge w ec sc ≤
    NL.length * (NL.length * (NL.length * (E + NL.length + 5) + 4)) +
      NL.length * (S + NL.length + 3) + NL.length + 4 := by
  have h1 := layerCost_le NL mid tgt edge w ec hE NL.length
  have h2 := sum_map_le NL (fun x => sc x + lookCost (layer NL mid tgt edge w NL.length) + 2)
    (S + NL.length + 3) (fun x hx => by
      have := hS x hx
      have := length_layer NL mid tgt edge w NL.length
      unfold lookCost; omega)
  unfold minPathLCost pickSrcCost
  omega
end ULHC.MP
