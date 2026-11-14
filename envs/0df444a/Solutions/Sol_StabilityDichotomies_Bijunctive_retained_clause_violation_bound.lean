-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.retained_clause_violation_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:48:16.105596+00:00
-- url     : https://prove2.me/submissions/54780a84-35e9-4d7c-b0c7-be334c374fb2

import Theorems.Thm_StabilityDichotomies_Bijunctive_retained_clause_positive_shift_violation_bound
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private theorem finite_independent_exponential_positive_ae {α : Type} [Fintype α]
    (β : ℝ) (hβ : 0 < β) :
    ∀ᵐ δ ∂(Measure.pi (fun _ : α => expMeasure β)), ∀ i, 0 < δ i := by
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  have hreal : (expMeasure β).real (Iic 0) = 0 := by
    rw [← cdf_eq_real]
    simpa using cdf_expMeasure_eq hβ 0
  have hzero : (expMeasure β) (Iic 0) = 0 := by
    have h := (ENNReal.toReal_eq_zero_iff _).mp hreal
    exact h.resolve_right (measure_ne_top _ _)
  have hone : ∀ᵐ x ∂(expMeasure β), 0 < x := by
    rw [ae_iff]
    have hset : {x : ℝ | ¬0 < x} = Iic 0 := by ext x; simp
    rw [hset]
    exact hzero
  apply ae_all_iff.mpr
  intro i
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : α => expMeasure β) (i := i)) hone

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (hF : Satisfiable F)
    (hsub : ∀ c ∈ G.constraints, c ∈ F.constraints)
    (c : Constraint Γ V) (hc : c ∈ G.constraints)
    (q : Clause (Fin c.rel.val.arity)) (hq : q ∈ rep.clauses c.rel)
    (ht : (substituteClause c q).1 ≠ literalNeg (substituteClause c q).2)
    (β : ℝ) (hβ : 0 < β) :
    ((Measure.pi (fun _ : Literal V => expMeasure β))
      {δ : Literal V → ℝ | ¬ clauseSatisfied (fun v => decide (literalScore rep G F δ (v,false) <
          literalScore rep G F δ (v,true))) (substituteClause c q)}).toReal ≤
      1 - Real.exp (-β) := by
  have h := retained_clause_positive_shift_violation_bound rep G F hF hsub c hc q hq ht β hβ
  have heq : (Measure.pi (fun _ : Literal V => expMeasure β))
      {δ : Literal V → ℝ | ¬ clauseSatisfied (fun v => decide (literalScore rep G F δ (v,false) <
          literalScore rep G F δ (v,true))) (substituteClause c q)} =
      (Measure.pi (fun _ : Literal V => expMeasure β))
      {δ : Literal V → ℝ | (∀ a, 0 < δ a) ∧ ¬ clauseSatisfied (fun v => decide
          (literalScore rep G F δ (v,false) < literalScore rep G F δ (v,true))) (substituteClause c q)} := by
    apply measure_congr
    filter_upwards [finite_independent_exponential_positive_ae (α := Literal V) β hβ] with δ hδ
    apply propext
    change (¬ clauseSatisfied (fun v => decide (literalScore rep G F δ (v,false) < literalScore rep G F δ (v,true))) (substituteClause c q)) ↔
      ((∀ a : Literal V, 0 < δ a) ∧ ¬ clauseSatisfied (fun v => decide (literalScore rep G F δ (v,false) < literalScore rep G F δ (v,true))) (substituteClause c q))
    exact ⟨fun hh => ⟨hδ,hh⟩, And.right⟩
  rw [heq]
  exact h
