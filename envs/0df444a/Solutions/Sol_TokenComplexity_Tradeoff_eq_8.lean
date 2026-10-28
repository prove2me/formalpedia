-- Prove2me | solution 1 for TokenComplexity.Tradeoff.eq_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T00:53:20.119119+00:00
-- url     : https://prove2.me/submissions/3811df96-0377-4770-85eb-e988968ae233

import Mathlib
import Definitions.Def_TokenComplexity_Tradeoff_Model

open Finset TokenComplexity.Tradeoff in
theorem solution {n : ℕ} {Prompt : Type} (B : Benchmark n Prompt) (τ : Fin n → ℕ∞)
    (hA1 : TokenComplexityHyp B τ) (P : Prompt) :
    accuracy B P = ((univ.filter (fun i => τ i ≤ (B.len P i : ℕ∞))).card : ℝ) / n := by
  unfold accuracy
  rw [Finset.filter_congr (fun i _ => hA1 P i)]
