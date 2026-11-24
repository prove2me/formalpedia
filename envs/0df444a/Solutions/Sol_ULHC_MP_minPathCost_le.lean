-- Prove2me | solution 1 for ULHC.MP.minPathCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:24:47.167858+00:00
-- url     : https://prove2.me/submissions/806ee31a-47b0-48f3-86d5-b48a38001d15

import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_CostMinPath
import Theorems.Thm_ULHC_MP_minPathLCost_le

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type} [DecidableEq α]
namespace ULHC.MP
theorem _root_.solution {β : Type} [LinearOrder β] (N : Finset β) (mid tgt : β → Bool)
    (edge : β → β → Bool) (w : β → ℕ) (ec : β → β → ℕ) (sc : β → ℕ) {E S : ℕ}
    (hE : ∀ x ∈ N, ∀ y ∈ N, ec x y ≤ E) (hS : ∀ x ∈ N, sc x ≤ S) :
    minPathCost N mid tgt edge w ec sc ≤
      N.card ^ 2 + N.card * (N.card * (N.card * (E + N.card + 5) + 4)) +
        N.card * (S + N.card + 3) + N.card + 4 := by
  have h := minPathLCost_le (N.sort (· ≤ ·)) mid tgt edge w ec sc
    (fun x hx y hy => hE x (by simpa using hx) y (by simpa using hy))
    (fun x hx => hS x (by simpa using hx))
  rw [Finset.length_sort] at h
  unfold minPathCost
  omega
end ULHC.MP
