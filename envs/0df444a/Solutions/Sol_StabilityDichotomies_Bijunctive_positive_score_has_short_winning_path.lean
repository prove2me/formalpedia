-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.positive_score_has_short_winning_path
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:06:05.174592+00:00
-- url     : https://prove2.me/submissions/1be98925-870e-4b4c-b8c0-b78f210655b4

import Theorems.Thm_StabilityDichotomies_Bijunctive_positive_score_has_maximizing_root
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (δ : Literal V → ℝ)
    (target : Literal V) (hpos : (0 : WithBot ℝ) < literalScore rep G F δ target) :
    ∃ root : Literal V, ∃ n : ℕ, feasibleLiteral F root ∧
      implicationDistance rep G root target = some n ∧
      literalScore rep G F δ target = ((δ root - n : ℝ) : WithBot ℝ) ∧
      (n : ℝ) < δ root := by
  obtain ⟨root,n,hf,hd,heq,hmax⟩ := positive_score_has_maximizing_root rep G F δ target hpos
  refine ⟨root,n,hf,hd,heq,?_⟩
  rw [heq] at hpos
  have hh : (0 : ℝ) < δ root - n := by exact_mod_cast hpos
  linarith
