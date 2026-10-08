-- Prove2me | solution 1 for RhinViola.normalizedLogLimsupEventuallyUpper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T23:22:31.708139+00:00
-- url     : https://prove2.me/submissions/3659b3a3-66f1-40ec-a96b-6f45e415e606

import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic

open Filter

theorem solution
    (ρ δ : ℝ) (g : ℕ → ℝ)
    (hδ : 0 < δ)
    (hbounded : IsBoundedUnder (· ≤ ·) atTop g)
    (hlimsup : limsup g atTop ≤ ρ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → g n ≤ ρ + δ := by
  have hupper :
      ∀ᶠ n : ℕ in atTop, g n < ρ + δ :=
    eventually_lt_add_pos_of_limsup_le hbounded hlimsup hδ
  have hupper' :
      ∀ᶠ n : ℕ in atTop, g n ≤ ρ + δ :=
    hupper.mono fun _ hn => hn.le
  exact Filter.eventually_atTop.1 hupper'
