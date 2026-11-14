-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.bijunctive_has_two_cnf_representation
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:50:36.983196+00:00
-- url     : https://prove2.me/submissions/72c22aac-9d73-480b-8791-90e46a248214

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
import Theorems.Thm_StabilityDichotomies_Bijunctive_majority_pairwise_extension
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private abbrev Pattern (n : ℕ) := (Fin n × Fin n) × (Bool × Bool)
private def forbidden {n : ℕ} (R : Finset (Fin n → Bool)) (t : Pattern n) : Prop :=
  ¬ ∃ y ∈ R, y t.1.1 = t.2.1 ∧ y t.1.2 = t.2.2
private def patternClause {n : ℕ} (t : Pattern n) : Clause (Fin n) :=
  ((t.1.1, !t.2.1), (t.1.2, !t.2.2))
private def relationClauses (R : Relation) : List (Clause (Fin R.arity)) :=
  ((Finset.univ : Finset (Pattern R.arity)).filter (forbidden R.tuples)).toList.map patternClause

private theorem relationClauses_correct (R : Relation)
    (hR : ∀ a b c, a ∈ R.tuples → b ∈ R.tuples → c ∈ R.tuples →
      (fun i => (a i && b i) || (a i && c i) || (b i && c i)) ∈ R.tuples)
    (x : Fin R.arity → Bool) :
    x ∈ R.tuples ↔ ∀ q ∈ relationClauses R, clauseSatisfied x q := by
  constructor
  · intro hx q hq
    simp only [relationClauses, List.mem_map, Finset.mem_toList, Finset.mem_filter,
      Finset.mem_univ, true_and] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    by_contra hbad
    have hp : x t.1.1 = t.2.1 ∧ x t.1.2 = t.2.2 := by
      simp only [clauseSatisfied, patternClause, literalValue, not_or] at hbad
      constructor <;> cases h1 : x t.1.1 <;> cases h2 : x t.1.2 <;>
        cases h3 : t.2.1 <;> cases h4 : t.2.2 <;> simp_all
    exact ht ⟨x,hx,hp⟩
  · intro hx
    apply majority_pairwise_extension R.tuples R.tuples_nonempty hR x
    intro i j
    by_contra hno
    let t : Pattern R.arity := ((i,j),(x i,x j))
    have ht : forbidden R.tuples t := hno
    have hq : patternClause t ∈ relationClauses R := by
      unfold relationClauses
      apply List.mem_map.mpr
      refine ⟨t, ?_, rfl⟩
      rw [Finset.mem_toList, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ht⟩
    have hb := hx (patternClause t) hq
    simp [clauseSatisfied, patternClause, literalValue, t] at hb

theorem solution (Γ : Language)
    (hΓ : ∀ R ∈ Γ.relations, ∀ x y z : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples → z ∈ R.tuples →
      (fun i => (x i && y i) || (x i && z i) || (y i && z i)) ∈ R.tuples) :
    Nonempty (TwoCNFRepresentation Γ) := by
  classical
  let f : ∀ R : Γ.Member, List (Clause (Fin R.val.arity)) := fun R => relationClauses R.val
  let N : ℕ := 1 + Γ.relations.sup (fun R => (relationClauses R).length)
  refine ⟨⟨f, ?_, N, ?_, ?_⟩⟩
  · intro R x
    exact relationClauses_correct R.val (hΓ R.val R.property) x
  · dsimp [N]; omega
  · intro R
    have hh : (f R).length ≤ Γ.relations.sup (fun S => (relationClauses S).length) := by
      exact Finset.le_sup (f := fun S : Relation => (relationClauses S).length) R.property
    dsimp [N]
    omega
