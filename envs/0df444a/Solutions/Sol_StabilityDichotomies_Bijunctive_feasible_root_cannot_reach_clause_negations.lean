-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.feasible_root_cannot_reach_clause_negations
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:10:33.70146+00:00
-- url     : https://prove2.me/submissions/be01c8e5-8433-49d2-a7e3-29044d2550d9

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private theorem literal_value_neg {V : Type} (x : V → Bool) (a : Literal V) :
    literalValue x (literalNeg a) = !(literalValue x a) := by
  rcases a with ⟨v,b⟩
  cases hx : x v <;> cases b <;> simp [literalValue, literalNeg, hx]

private theorem implication_arc_preserves_solution {Γ : Language} {V : Type}
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (x : V → Bool) (hx : Solution I x)
    (a b : Literal V) (hab : implicationArc rep I a b) (ha : literalValue x a = true) :
    literalValue x b = true := by
  obtain ⟨c,hc,q,hq,ht,himp⟩ := hab
  have hc' := (rep.correct c.rel (fun i => x (c.scope i))).mp (hx c hc) q hq
  have hz : clauseSatisfied x (substituteClause c q) := by
    simpa [clauseSatisfied, literalValue, substituteClause] using hc'
  rcases himp with h | h
  · obtain ⟨rfl,rfl⟩ := h
    simp only [literal_value_neg] at ha
    rcases hz with hz | hz
    · rw [hz] at ha
      contradiction
    · exact hz
  · obtain ⟨rfl,rfl⟩ := h
    simp only [literal_value_neg] at ha
    rcases hz with hz | hz
    · exact hz
    · rw [hz] at ha
      contradiction

private theorem implication_walk_preserves_solution {Γ : Language} {V : Type}
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (x : V → Bool) (hx : Solution I x)
    (n : ℕ) (a b : Literal V) (hab : WalkLength (implicationArc rep I) n a b)
    (ha : literalValue x a = true) : literalValue x b = true := by
  induction hab with
  | zero => exact ha
  | @step n a b c hArc hWalk ih =>
    exact ih (implication_arc_preserves_solution rep I x hx a b hArc ha)

theorem solution {Γ : Language} {V : Type}
    (rep : TwoCNFRepresentation Γ) (I₁ I₂ : Instance Γ V)
    (hsub : ∀ c ∈ I₁.constraints, c ∈ I₂.constraints)
    (c : Constraint Γ V) (hc : c ∈ I₁.constraints)
    (q : Clause (Fin c.rel.val.arity)) (hq : q ∈ rep.clauses c.rel)
    (root : Literal V) (hroot : feasibleLiteral I₂ root) :
    ¬ (∃ n m : ℕ, WalkLength (implicationArc rep I₁) n root (literalNeg (substituteClause c q).1) ∧
      WalkLength (implicationArc rep I₁) m root (literalNeg (substituteClause c q).2)) := by
  obtain ⟨x,hx,hrootx⟩ := hroot
  have hx1 : Solution I₁ x := by
    intro d hd
    exact hx d (hsub d hd)
  have hc' := (rep.correct c.rel (fun i => x (c.scope i))).mp (hx c (hsub c hc)) q hq
  have hz : clauseSatisfied x (substituteClause c q) := by
    simpa [clauseSatisfied, literalValue, substituteClause] using hc'
  rintro ⟨n,m,ha,hb⟩
  have h1 := implication_walk_preserves_solution rep I₁ x hx1 n root
    (literalNeg (substituteClause c q).1) ha hrootx
  have h2 := implication_walk_preserves_solution rep I₁ x hx1 m root
    (literalNeg (substituteClause c q).2) hb hrootx
  rw [literal_value_neg] at h1 h2
  rcases hz with hz | hz
  · rw [hz] at h1
    contradiction
  · rw [hz] at h2
    contradiction
