-- Prove2me | solution 1 for ULHC.MP.layerCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:09.479554+00:00
-- url     : https://prove2.me/submissions/1c79d455-2886-4a9c-9257-b8b185a60054

import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_CostMinPath
import Theorems.Thm_ULHC_MP_length_layer
import Theorems.Thm_ULHC_MP_nextCost_le

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type} [DecidableEq α]
variable (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
  (ec : α → α → ℕ) (sc : α → ℕ) {E S : ℕ}
  (hE : ∀ x ∈ NL, ∀ y ∈ NL, ec x y ≤ E) (hS : ∀ x ∈ NL, sc x ≤ S)
include hE
namespace ULHC.MP
theorem _root_.solution : ∀ k, layerCost NL mid tgt edge w ec k ≤
    1 + k * (NL.length * (NL.length * (E + NL.length + 5) + 4)) := by
  intro k
  induction k with
  | zero => simp [layerCost]
  | succ k ih =>
    simp only [layerCost]
    have := nextCost_le NL mid tgt ec hE _ (length_layer NL mid tgt edge w k)
    rw [Nat.succ_mul]
    omega
end ULHC.MP
