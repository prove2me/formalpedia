-- Prove2me | solution 1 for ULHC.MP.stepCost_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:13:43.873411+00:00
-- url     : https://prove2.me/submissions/c5bc0b87-ef46-403e-a98e-a104256a9c30

import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_CostMinPath
import Theorems.Thm_P2M_ULHC_MP_lsum_mono__0cdf42948454

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type} [DecidableEq α]
variable (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
  {ec ec' : α → α → ℕ} {sc sc' : α → ℕ} (hE : ∀ x y, ec x y ≤ ec' x y) (hS : ∀ x, sc x ≤ sc' x)
include hE
omit [DecidableEq α]
namespace ULHC.MP
theorem _root_.solution (tbl : List (α × Option (ℕ × List α))) (x : α) :
    stepCost NL mid tgt ec tbl x ≤ stepCost NL mid tgt ec' tbl x := by
  have := lsum_mono' NL (fun y => ec x y + lookCost tbl + 4) (fun y => ec' x y + lookCost tbl + 4)
    (fun y => by have := hE x y; omega)
  unfold stepCost
  split_ifs <;> omega
end ULHC.MP
