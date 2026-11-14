-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.violated_clause_has_close_root_maxima
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:42:30.251205+00:00
-- url     : https://prove2.me/submissions/d2fb2908-4cb7-4d47-81e9-59295ea4dec5

import Theorems.Thm_StabilityDichotomies_Bijunctive_feasible_root_cannot_reach_clause_negations
import Theorems.Thm_StabilityDichotomies_Bijunctive_violated_clause_close_scores
import Theorems.Thm_StabilityDichotomies_Bijunctive_positive_score_has_maximizing_root
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private theorem distance_walk {Γ : Language} {V : Type} (rep : TwoCNFRepresentation Γ)
    (G : Instance Γ V) (a b : Literal V) (n : ℕ)
    (hd : implicationDistance rep G a b = some n) :
    WalkLength (implicationArc rep G) n a b := by
  unfold implicationDistance at hd
  split at hd
  next h =>
    have hn : Nat.find h = n := Option.some.inj hd
    simpa [← hn] using Nat.find_spec h
  next h => simp at hd

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (δ : Literal V → ℝ)
    (hsub : ∀ c ∈ G.constraints, c ∈ F.constraints)
    (hpos : ∀ v : V, ∃ b : Bool, (0 : WithBot ℝ) < literalScore rep G F δ (v,b))
    (c : Constraint Γ V) (hc : c ∈ G.constraints)
    (q : Clause (Fin c.rel.val.arity)) (hq : q ∈ rep.clauses c.rel)
    (ht : (substituteClause c q).1 ≠ literalNeg (substituteClause c q).2)
    (hviol : ¬ clauseSatisfied (fun v => decide (literalScore rep G F δ (v,false) <
      literalScore rep G F δ (v,true))) (substituteClause c q)) :
    let a := literalNeg (substituteClause c q).1
    let b := literalNeg (substituteClause c q).2
    ∃ u v : Literal V, ∃ n m : ℕ, u ≠ v ∧ feasibleLiteral F u ∧ feasibleLiteral F v ∧
      implicationDistance rep G u a = some n ∧ implicationDistance rep G v b = some m ∧
      (∀ r k, feasibleLiteral F r → implicationDistance rep G r a = some k → δ r - k ≤ δ u - n) ∧
      (∀ r k, feasibleLiteral F r → implicationDistance rep G r b = some k → δ r - k ≤ δ v - m) ∧
      (δ u - n) - (δ v - m) ≤ 1 ∧ (δ v - m) - (δ u - n) ≤ 1 := by
  dsimp only
  let a := literalNeg (substituteClause c q).1
  let b := literalNeg (substituteClause c q).2
  have hclose := violated_clause_close_scores rep G F δ hpos c hc q hq ht hviol
  change (0 : WithBot ℝ) < literalScore rep G F δ a ∧
    (0 : WithBot ℝ) < literalScore rep G F δ b ∧
    literalScore rep G F δ a ≤ literalScore rep G F δ b + ((1 : ℝ) : WithBot ℝ) ∧
    literalScore rep G F δ b ≤ literalScore rep G F δ a + ((1 : ℝ) : WithBot ℝ) at hclose
  obtain ⟨u,n,hfu,hdu,hsu,hmu⟩ := positive_score_has_maximizing_root rep G F δ a hclose.1
  obtain ⟨v,m,hfv,hdv,hsv,hmv⟩ := positive_score_has_maximizing_root rep G F δ b hclose.2.1
  have hne : u ≠ v := by
    intro h; subst v
    exact feasible_root_cannot_reach_clause_negations rep G F hsub c hc q hq u hfu
      ⟨n,m,distance_walk rep G u a n hdu,distance_walk rep G u b m hdv⟩
  refine ⟨u,v,n,m,hne,hfu,hfv,hdu,hdv,hmu,hmv,?_,?_⟩
  · rw [hsu,hsv] at hclose
    have h := hclose.2.2.1
    norm_cast at h
    linarith
  · rw [hsu,hsv] at hclose
    have h := hclose.2.2.2
    norm_cast at h
    linarith
