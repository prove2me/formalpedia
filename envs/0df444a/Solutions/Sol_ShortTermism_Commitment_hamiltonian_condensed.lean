-- Prove2me | solution 1 for ShortTermism.Commitment.hamiltonian_condensed
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T03:52:05.225278+00:00
-- url     : https://prove2.me/submissions/84940ec7-e848-434c-8c8c-578ac5afcb83

import Mathlib
import Definitions.Def_ShortTermism_Commitment_Model

open ShortTermism.Commitment

theorem solution (P : Params) (hP : P.Standing) (C δ a e f1 f2 : ℝ) :
    hjbIntegrand P C δ a e f1 f2
      = δ * condensedObj P δ a e f1 + δ * P.ψ - (1 - P.τ) * C + P.φ * δ * f1
        + 1 / 2 * P.σδ ^ 2 * δ ^ 2 * f2 := by
  unfold hjbIntegrand condensedObj Ahat Bhat Dhat incentiveSigma
  ring
