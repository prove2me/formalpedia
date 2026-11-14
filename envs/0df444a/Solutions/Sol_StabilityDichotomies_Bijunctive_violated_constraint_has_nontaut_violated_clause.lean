-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.violated_constraint_has_nontaut_violated_clause
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:58:59.069034+00:00
-- url     : https://prove2.me/submissions/0c9f4fa1-22d2-4581-ad5b-598d880e50c4

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private theorem literal_value_neg {V : Type} (x : V → Bool) (a : Literal V) :
    literalValue x (literalNeg a) = !(literalValue x a) := by
  rcases a with ⟨v,b⟩
  cases hx : x v <;> cases b <;> simp [literalValue, literalNeg, hx]

theorem solution {Γ : Language} {V : Type}
    (rep : TwoCNFRepresentation Γ) (c : Constraint Γ V) (x : V → Bool)
    (hviol : ¬ c.Satisfied x) :
    ∃ q ∈ rep.clauses c.rel,
      (substituteClause c q).1 ≠ literalNeg (substituteClause c q).2 ∧
      ¬ clauseSatisfied x (substituteClause c q) := by
  have hnot : ¬ ∀ q ∈ rep.clauses c.rel, clauseSatisfied x (substituteClause c q) := by
    intro hall
    apply hviol
    apply (rep.correct c.rel (fun i => x (c.scope i))).mpr
    intro q hq
    have h := hall q hq
    simpa [clauseSatisfied,literalValue,substituteClause] using h
  push_neg at hnot
  obtain ⟨q,hq,hqv⟩ := hnot
  refine ⟨q,hq,?_,hqv⟩
  intro ht
  have h := literal_value_neg x (substituteClause c q).2
  rw [← ht] at h
  have ha : literalValue x (substituteClause c q).1 ≠ true := fun hh => hqv (Or.inl hh)
  have hb : literalValue x (substituteClause c q).2 ≠ true := fun hh => hqv (Or.inr hh)
  cases h1 : literalValue x (substituteClause c q).1 <;>
    cases h2 : literalValue x (substituteClause c q).2 <;> simp_all
