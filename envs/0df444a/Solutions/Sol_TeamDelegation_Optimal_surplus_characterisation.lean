-- Prove2me | solution 1 for TeamDelegation.Optimal.surplus_characterisation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T13:43:13.971638+00:00
-- url     : https://prove2.me/submissions/8c5df00a-be41-4255-843b-8e3ec067509f

import Mathlib
import Definitions.Def_TeamDelegation_Optimal_Model

open TeamDelegation.Optimal

theorem solution (P : Params) (hS : P.Standing)
    (hA1 : P.Assumption1) (c1A c1B ΔA ΔB wA wB : ℝ)
    (hA : ΔA ≤ DeltaCritA P) (hsum : 0 ≤ ΔA + ΔB) :
    SurplusMax P (Costs.ofDeltas c1A c1B ΔA ΔB) .deleg wA wB ↔
      SurplusConstraints P (wA + wB) (ΔA + ΔB) := by
  unfold SurplusMax SurplusConstraints
  constructor
  · intro h
    have e1 := h 0 (0, true) false trivial
    have e2 := h 0 (0, false) false trivial
    have e3 := h 0 (1, true) true trivial
    have e4 := h 0 (1, true) false trivial
    have e5 := h 0 (1, false) false trivial
    have e6 := h 1 (0, true) true trivial
    have e7 := h 1 (0, true) false trivial
    have e8 := h 1 (0, false) false trivial
    simp [payA, payB, succProb, workers, desiredA, Costs.ofDeltas] at e1 e2 e3 e4 e5 e6 e7 e8
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨h59, h60, h61, h62, h63, h64, h65, h66⟩ k a b _
    rcases a with ⟨m, x⟩
    fin_cases k <;> fin_cases m <;> cases x <;> cases b <;>
      simp [payA, payB, succProb, workers, desiredA, Costs.ofDeltas] <;> linarith
