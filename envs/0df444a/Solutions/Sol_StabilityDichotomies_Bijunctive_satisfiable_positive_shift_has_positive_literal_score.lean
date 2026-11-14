-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.satisfiable_positive_shift_has_positive_literal_score
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:10:32.960226+00:00
-- url     : https://prove2.me/submissions/6d77053c-cc5a-4513-8fc6-3bc11469bd08

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private theorem literal_score_candidate_lower {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (δ : Literal V → ℝ)
    (root target : Literal V) (n : ℕ) (hr : feasibleLiteral F root)
    (hd : implicationDistance rep G root target = some n) :
    ((δ root - n : ℝ) : WithBot ℝ) ≤ literalScore rep G F δ target := by
  unfold literalScore
  apply Finset.le_sup_of_le (Finset.mem_univ root)
  simp [hr,hd]


theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (hF : Satisfiable F)
    (δ : Literal V → ℝ) (hδ : ∀ a, 0 < δ a) (v : V) :
    ∃ b : Bool, (0 : WithBot ℝ) < literalScore rep G F δ (v,b) := by
  obtain ⟨x,hx⟩ := hF
  let root : Literal V := (v,x v)
  have hr : feasibleLiteral F root := by
    refine ⟨x,hx,?_⟩
    simp [literalValue,root]
  have hreach : ∃ n : ℕ, WalkLength (implicationArc rep G) n root root :=
    ⟨0, WalkLength.zero root⟩
  have hzero : Nat.find hreach = 0 := by
    have h := Nat.find_min' hreach (WalkLength.zero root)
    omega
  have hd : implicationDistance rep G root root = some 0 := by
    simp [implicationDistance,hreach,hzero]
  have hlower := literal_score_candidate_lower rep G F δ root root 0 hr hd
  refine ⟨x v, ?_⟩
  have hp : (0 : WithBot ℝ) < ((δ root : ℝ) : WithBot ℝ) := by exact_mod_cast hδ root
  exact hp.trans_le (by simpa [root] using hlower)
