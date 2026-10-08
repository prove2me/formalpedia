-- Prove2me | solution 1 for WeightedRootIntegralIdentity.monotone_on_range_of_adjacent
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-13T15:34:34.10147+00:00
-- url     : https://prove2.me/submissions/61363452-73ca-479b-ac0d-7e47e7b4655c

import Mathlib

theorem solution
    (n : ℕ) (a : ℕ → ℝ)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1)) :
    ∀ i j, i < j → j < n → a i ≤ a j := by
  intro i j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hij hj
      cases j with
      | zero => omega
      | succ t =>
          by_cases hit : i = t
          · subst i
            simpa [Nat.succ_eq_add_one] using hmono t (by omega)
          · have hitlt : i < t := by omega
            have hleft : a i ≤ a t :=
              ih t (Nat.lt_succ_self t) hitlt (by omega)
            have hright : a t ≤ a (Nat.succ t) := by
              simpa [Nat.succ_eq_add_one] using hmono t (by omega)
            exact hleft.trans hright
