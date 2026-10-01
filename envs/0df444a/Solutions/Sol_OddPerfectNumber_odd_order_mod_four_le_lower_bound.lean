-- Prove2me | solution 1 for OddPerfectNumber.odd_order_mod_four_le_lower_bound
-- status  : ACCEPTED   (disprove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T20:01:56.263637+00:00
-- url     : https://prove2.me/submissions/cd593936-26b4-4233-8f18-3625ebc5f950

import Mathlib

theorem solution : ¬ (∀ {p t n : Nat}, (hp : p.Prime) → (hp4 : p % 4 = 1) →
    (hpt : Not (Dvd.dvd p t)) → (hnodd : ¬ Even n) →
    (hord : 1 < orderOf (t : ZMod p)) → (hdiv : Dvd.dvd (orderOf (t : ZMod p)) n) →
    (p - 1) / 4 ≤ n) := by
  intro h
  have ho : orderOf (10 : ZMod 37) = 3 := by
    apply (orderOf_eq_iff (by norm_num : 0 < 3)).2
    constructor
    · decide
    · intro m hm hm0
      interval_cases m <;> decide
  have hc := h (p := 37) (t := 10) (n := 3) (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by simpa [ho]) (by simp [ho])
  norm_num at hc
