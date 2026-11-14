-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.feasible_root_cannot_reach_opposites
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:50:37.563666+00:00
-- url     : https://prove2.me/submissions/9f82da93-5bee-4881-90cc-7988d376a13f

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
    (root target : Literal V) (hroot : feasibleLiteral I₂ root) :
    ¬ (∃ n m : ℕ, WalkLength (implicationArc rep I₁) n root target ∧
      WalkLength (implicationArc rep I₁) m root (literalNeg target)) := by
  obtain ⟨x,hx,hrootx⟩ := hroot
  have hx1 : Solution I₁ x := by
    intro c hc
    exact hx c (hsub c hc)
  rintro ⟨n,m,ha,hb⟩
  have ht := implication_walk_preserves_solution rep I₁ x hx1 n root target ha hrootx
  have hn := implication_walk_preserves_solution rep I₁ x hx1 m root (literalNeg target) hb hrootx
  rw [literal_value_neg, ht] at hn
  contradiction
