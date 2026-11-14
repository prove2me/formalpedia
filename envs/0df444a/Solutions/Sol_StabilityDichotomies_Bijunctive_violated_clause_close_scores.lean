-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.violated_clause_close_scores
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:13:29.200673+00:00
-- url     : https://prove2.me/submissions/91d5506d-0369-48aa-9712-81081a7d8464

import Theorems.Thm_StabilityDichotomies_Bijunctive_implication_score_arc_bound
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private def scoreAssignment {V : Type} (S : Literal V → WithBot ℝ) : V → Bool :=
  fun v => decide (S (v,false) < S (v,true))

private theorem false_literal_score_order {V : Type} (S : Literal V → WithBot ℝ)
    (hpos : ∀ v, ∃ b : Bool, (0 : WithBot ℝ) < S (v,b))
    (a : Literal V) (hfalse : literalValue (scoreAssignment S) a = false) :
    S a ≤ S (literalNeg a) ∧ (0 : WithBot ℝ) < S (literalNeg a) := by
  obtain ⟨v,b⟩ := a
  cases b with
  | false =>
    have hgt : S (v,false) < S (v,true) := by
      simpa [literalValue,scoreAssignment] using hfalse
    refine ⟨le_of_lt hgt, ?_⟩
    obtain ⟨b,hb⟩ := hpos v
    cases b with
    | false => exact hb.trans hgt
    | true => exact hb
  | true =>
    have hle : S (v,true) ≤ S (v,false) := by
      apply le_of_not_gt
      intro hgt
      simp [literalValue,scoreAssignment,hgt] at hfalse
    refine ⟨hle, ?_⟩
    obtain ⟨b,hb⟩ := hpos v
    cases b with
    | false => exact hb
    | true => exact hb.trans_le hle

private theorem violated_retained_clause_has_close_opposite_scores {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (δ : Literal V → ℝ)
    (hpos : ∀ v : V, ∃ b : Bool, (0 : WithBot ℝ) < literalScore rep G F δ (v,b))
    (c : Constraint Γ V) (hc : c ∈ G.constraints)
    (q : Clause (Fin c.rel.val.arity)) (hq : q ∈ rep.clauses c.rel)
    (ht : (substituteClause c q).1 ≠ literalNeg (substituteClause c q).2)
    (hviol : ¬ clauseSatisfied (scoreAssignment (literalScore rep G F δ)) (substituteClause c q)) :
    let a := (substituteClause c q).1
    let b := (substituteClause c q).2
    (0 : WithBot ℝ) < literalScore rep G F δ (literalNeg a) ∧
    (0 : WithBot ℝ) < literalScore rep G F δ (literalNeg b) ∧
    literalScore rep G F δ (literalNeg a) ≤ literalScore rep G F δ (literalNeg b) + ((1 : ℝ) : WithBot ℝ) ∧
    literalScore rep G F δ (literalNeg b) ≤ literalScore rep G F δ (literalNeg a) + ((1 : ℝ) : WithBot ℝ) := by
  dsimp only
  let a := (substituteClause c q).1
  let b := (substituteClause c q).2
  let S := literalScore rep G F δ
  have hv1 : literalValue (scoreAssignment S) a = false := by
    have hh : literalValue (scoreAssignment S) a ≠ true := by
      intro ht1; exact hviol (Or.inl ht1)
    cases he : literalValue (scoreAssignment S) a <;> simp_all
  have hv2 : literalValue (scoreAssignment S) b = false := by
    have hh : literalValue (scoreAssignment S) b ≠ true := by
      intro ht2; exact hviol (Or.inr ht2)
    cases he : literalValue (scoreAssignment S) b <;> simp_all
  have h1 := false_literal_score_order S hpos a hv1
  have h2 := false_literal_score_order S hpos b hv2
  have harc1 : implicationArc rep G (literalNeg a) b := by
    refine ⟨c,hc,q,hq,ht,?_⟩
    exact Or.inl ⟨rfl,rfl⟩
  have harc2 : implicationArc rep G (literalNeg b) a := by
    refine ⟨c,hc,q,hq,ht,?_⟩
    exact Or.inr ⟨rfl,rfl⟩
  have hs1 := implication_score_arc_bound rep G F δ (literalNeg a) b harc1
  have hs2 := implication_score_arc_bound rep G F δ (literalNeg b) a harc2
  refine ⟨h1.2,h2.2,?_,?_⟩
  · exact hs1.trans (add_le_add_left h2.1 _)
  · exact hs2.trans (add_le_add_left h1.1 _)


theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (δ : Literal V → ℝ)
    (hpos : ∀ v : V, ∃ b : Bool, (0 : WithBot ℝ) < literalScore rep G F δ (v,b))
    (c : Constraint Γ V) (hc : c ∈ G.constraints)
    (q : Clause (Fin c.rel.val.arity)) (hq : q ∈ rep.clauses c.rel)
    (ht : (substituteClause c q).1 ≠ literalNeg (substituteClause c q).2)
    (hviol : ¬ clauseSatisfied (fun v => decide (literalScore rep G F δ (v,false) <
      literalScore rep G F δ (v,true))) (substituteClause c q)) :
    let a := (substituteClause c q).1
    let b := (substituteClause c q).2
    (0 : WithBot ℝ) < literalScore rep G F δ (literalNeg a) ∧
    (0 : WithBot ℝ) < literalScore rep G F δ (literalNeg b) ∧
    literalScore rep G F δ (literalNeg a) ≤ literalScore rep G F δ (literalNeg b) + ((1 : ℝ) : WithBot ℝ) ∧
    literalScore rep G F δ (literalNeg b) ≤ literalScore rep G F δ (literalNeg a) + ((1 : ℝ) : WithBot ℝ) := by
  apply violated_retained_clause_has_close_opposite_scores rep G F δ hpos c hc q hq ht
  unfold scoreAssignment at *
  exact hviol
