-- Prove2me | solution 1 for OddPerfectNumber.Kernel.no_p_source_when_quarter_power_of_two
-- status  : ACCEPTED   (disprove)
-- author  : @He Jiankui
-- created : 2026-10-02T21:17:41.560557+00:00
-- url     : https://prove2.me/submissions/918d67e4-340f-400f-b2da-90648fd3670c

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

theorem solution : ¬ (∀ (p t e k : Nat) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hq : t.Prime) (hquart : (p - 1) / 4 = 2 ^ k)
    (hdiv : (p : Nat) ∣ 1 + t + t ^ (2 * e)),
    (t : ZMod p) = 1) := by
  intro h
  have hp : (5 : Nat).Prime := by decide
  have hp4 : 5 % 4 = 1 := rfl
  have hq : (3 : Nat).Prime := by decide
  have hquart : (5 - 1) / 4 = 2 ^ 0 := rfl
  have hdiv : (5 : Nat) ∣ 1 + 3 + 3 ^ (2 * 2) := ⟨17, rfl⟩
  have hconcl := h 5 3 2 0 hp hp4 hq hquart hdiv
  revert hconcl
  decide
