-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.score_decreases_when_feasible_roots_shrink
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:22:26.499957+00:00
-- url     : https://prove2.me/submissions/b929db61-f68b-4bd2-af0a-c0a2ae172062

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F F' : Instance Γ V) (δ : Literal V → ℝ)
    (hsub : ∀ c ∈ F.constraints, c ∈ F'.constraints) (target : Literal V) :
    literalScore rep G F' δ target ≤ literalScore rep G F δ target := by
  have hfeas : ∀ r, feasibleLiteral F' r → feasibleLiteral F r := by
    intro r hr
    obtain ⟨x,hx,hxr⟩ := hr
    exact ⟨x,fun c hc => hx c (hsub c hc),hxr⟩
  unfold literalScore
  apply Finset.sup_le
  intro root hr
  by_cases hf : feasibleLiteral F' root
  · have hf' := hfeas root hf
    apply Finset.le_sup_of_le (Finset.mem_univ root)
    simp [hf,hf']
  · simp [hf]
