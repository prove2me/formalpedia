-- Prove2me | solution 1 for ULHC.MP.sum_map_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:54:07.521104+00:00
-- url     : https://prove2.me/submissions/eb3f122b-f28e-4335-af7c-32d954902524

import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_CostMinPath

set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type} [DecidableEq α]
namespace ULHC.MP
theorem _root_.solution {γ : Type} (l : List γ) (f : γ → ℕ) (b : ℕ) (h : ∀ x ∈ l, f x ≤ b) :
    (l.map f).sum ≤ l.length * b := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    have ha := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    omega
end ULHC.MP
