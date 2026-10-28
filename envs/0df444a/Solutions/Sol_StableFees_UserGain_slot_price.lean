-- Prove2me | solution 1 for StableFees.UserGain.slot_price
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:08:50.903295+00:00
-- url     : https://prove2.me/submissions/cd5f55ef-6832-4af2-a6df-a831b32bcc4d

import Mathlib
import Definitions.Def_StableFees_UserGain_Model

open StableFees.UserGain in
theorem solution (K m : ℕ) (hK : 2 ≤ K) (hm : K ≤ m)
    (Vbar v b : ℝ) (hv : v ∈ Set.Icc 0 Vbar) (hb : b ∈ Set.Icc 0 Vbar)
    (x : Fin m → ℝ) (hx : ∀ j, x j ∈ Set.Icc 0 Vbar)
    (hvalue : kthHighest x K ≤ v) :
    (kthHighest x K < b → kthHighest x (K - 1) ≤ b →
      payoff K v b x = v - kthHighest x (K - 1)) ∧
    (kthHighest x K < b → b < kthHighest x (K - 1) →
      payoff K v b x = v - b) := by
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · unfold payoff; rw [if_pos h1, min_eq_right h2]
  · unfold payoff; rw [if_pos h1, min_eq_left h2.le]
