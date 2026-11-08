-- Prove2me | solution 1 for PointRedemption.eq_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:55:21.303984+00:00
-- url     : https://prove2.me/submissions/22835e79-e6eb-4877-9b10-0c4a93464f73

import Mathlib
import Definitions.Def_PointRedemption_Model

open MeasureTheory ProbabilityTheory

open PointRedemption in
theorem solution (P : Params) (t y : ℕ) (ht : 1 ≤ t) (hy : 1 ≤ y) (p : ℝ) :
    P.J t p y =
      P.lam * P.βbar *
          (P.Fbar p * P.Gbar (p / P.q) * (p - P.Δ (t - 1) y) + P.I p * (P.R - P.Δ (t - 1) y)) +
        P.lam * P.β * (P.Fbar p * (p - P.Δ (t - 1) y)) + P.V (t - 1) y := by
  have hF : P.F p = 1 - P.Fbar p := by
    simp only [Params.Fbar, Params.F, LariviereIGFR.Char.survival]
    ring
  simp only [Params.J, Params.Jstep, Params.Δ, hF, Params.β]
  ring
