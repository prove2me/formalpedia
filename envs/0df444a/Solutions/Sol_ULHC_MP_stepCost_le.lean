-- Prove2me | solution 1 for ULHC.MP.stepCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:13:36.593708+00:00
-- url     : https://prove2.me/submissions/3d434e9d-d7ba-4472-8c3a-fe4314a76a65

import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_CostMinPath
import Theorems.Thm_ULHC_MP_sum_map_le

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type} [DecidableEq α]
variable (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
  (ec : α → α → ℕ) (sc : α → ℕ) {E S : ℕ}
  (hE : ∀ x ∈ NL, ∀ y ∈ NL, ec x y ≤ E) (hS : ∀ x ∈ NL, sc x ≤ S)
include hE
omit [DecidableEq α]
namespace ULHC.MP
theorem _root_.solution (tbl : List (α × Option (ℕ × List α))) (ht : tbl.length ≤ NL.length)
    {x : α} (hx : x ∈ NL) :
    stepCost NL mid tgt ec tbl x ≤ NL.length * (E + NL.length + 5) + 3 := by
  have h := sum_map_le NL (fun y => ec x y + lookCost tbl + 4) (E + NL.length + 5)
    (fun y hy => by have := hE x hx y hy; unfold lookCost; omega)
  unfold stepCost
  split_ifs <;> omega
end ULHC.MP
