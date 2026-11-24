-- Prove2me | solution 1 for P2M_ULHC_MP_lsum_mono__0cdf42948454
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:54:08.15839+00:00
-- url     : https://prove2.me/submissions/66af3f42-625c-405d-a009-823401a4f939

import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_CostMinPath

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type} [DecidableEq α]
variable (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
  {ec ec' : α → α → ℕ} {sc sc' : α → ℕ} (hE : ∀ x y, ec x y ≤ ec' x y) (hS : ∀ x, sc x ≤ sc' x)
namespace ULHC.MP
theorem _root_.solution {γ : Type} (l : List γ) (f g : γ → ℕ) (h : ∀ x, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a tf ih => simp only [List.map_cons, List.sum_cons]; exact Nat.add_le_add (h a) ih
end ULHC.MP
