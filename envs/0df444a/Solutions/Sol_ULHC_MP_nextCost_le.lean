-- Prove2me | solution 1 for ULHC.MP.nextCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:15:19.549719+00:00
-- url     : https://prove2.me/submissions/6ee6d01e-ecdb-4643-8449-9f61960a2937

import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_CostMinPath
import Theorems.Thm_ULHC_MP_sum_map_le
import Theorems.Thm_ULHC_MP_stepCost_le

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type} [DecidableEq α]
variable (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
  (ec : α → α → ℕ) (sc : α → ℕ) {E S : ℕ}
  (hE : ∀ x ∈ NL, ∀ y ∈ NL, ec x y ≤ E) (hS : ∀ x ∈ NL, sc x ≤ S)
include hE
omit [DecidableEq α]
namespace ULHC.MP
theorem _root_.solution (tbl : List (α × Option (ℕ × List α))) (ht : tbl.length ≤ NL.length) :
    nextCost NL mid tgt ec tbl ≤ NL.length * (NL.length * (E + NL.length + 5) + 4) :=
  sum_map_le NL _ _ (fun x hx => by
    have := stepCost_le NL mid tgt ec hE tbl ht hx; omega)
end ULHC.MP
