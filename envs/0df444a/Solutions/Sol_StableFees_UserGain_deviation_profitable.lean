-- Prove2me | solution 1 for StableFees.UserGain.deviation_profitable
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:06:52.938509+00:00
-- url     : https://prove2.me/submissions/2d42edf8-7c62-44af-ab42-9382d88ee1f0

import Mathlib
import Definitions.Def_StableFees_UserGain_Model

open StableFees.UserGain in
theorem solution (K m : ℕ) (hK : 2 ≤ K) (hm : K ≤ m)
    (Vbar v b : ℝ) (hv : v ∈ Set.Icc 0 Vbar) (hb : b ∈ Set.Icc 0 Vbar)
    (x : Fin m → ℝ) (hx : ∀ j, x j ∈ Set.Icc 0 Vbar)
    (hbelow : kthHighest x K < b)
    (hbetween : b < kthHighest x (K - 1))
    (habove : kthHighest x (K - 1) < v) :
    payoff K v b x = v - b ∧
    payoff K v v x = v - kthHighest x (K - 1) ∧
    payoff K v v x < payoff K v b x := by
  have h1 : payoff K v b x = v - b := by
    unfold payoff; rw [if_pos hbelow, min_eq_left hbetween.le]
  have h2 : payoff K v v x = v - kthHighest x (K - 1) := by
    unfold payoff; rw [if_pos (by linarith), min_eq_right habove.le]
  exact ⟨h1, h2, by rw [h1, h2]; linarith⟩
