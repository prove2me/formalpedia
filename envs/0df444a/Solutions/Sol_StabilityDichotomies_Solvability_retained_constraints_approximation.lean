-- Prove2me | solution 1 for StabilityDichotomies.Solvability.retained_constraints_approximation
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T04:56:57.015197+00:00
-- url     : https://prove2.me/submissions/7cb8e9b8-468c-4951-bf5a-a0e9cb5335fb

import Definitions.Def_StabilityDichotomies_Approximability_Core
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability

private theorem sum_violations {α β : Type} [Fintype β]
    (s : Multiset α) (p : β → α → Prop) [∀ x, DecidablePred (p x)] (w : β → ℝ) :
    (∑ x : β, w x * ((s.filter (p x)).card : ℝ)) =
      (s.map fun c => ∑ x : β, w x * (if p x c then 1 else 0)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    simp only [Multiset.filter_cons, Multiset.map_cons, Multiset.sum_cons]
    calc
      _ = ∑ x : β, (w x * (if p x a then 1 else 0) +
          w x * ((s.filter (p x)).card : ℝ)) := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hh : p x a <;> simp [hh, mul_add, add_comm]
      _ = _ := by rw [Finset.sum_add_distrib, ih]

private theorem sum_bounded {α : Type} (s : Multiset α) (f : α → ℝ) (ε : ℝ)
    (h : ∀ a ∈ s, f a ≤ ε) : (s.map f).sum ≤ ε * s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    have ha : f a ≤ ε := h a (Multiset.mem_cons_self a s)
    have hs : ∀ b ∈ s, f b ≤ ε := by
      intro b hb
      exact h b (Multiset.mem_cons_of_mem hb)
    have hr := ih hs
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add,
      Nat.cast_one, mul_add, mul_one] at *
    linarith

theorem solution
    {Γ : Language} {V : Type} [Fintype V] (I : Instance Γ V)
    (Ω : Type) [Fintype Ω] (μ : PMF Ω) (output : Ω → V → Bool)
    (retained : Ω → Constraint Γ V → Prop)
    (ε : ℝ)
    (hsatisfy : ∀ ω c, c ∈ I.constraints → retained ω c → c.Satisfied (output ω))
    (homit : ∀ c ∈ I.constraints,
      (∑ ω : Ω, (μ ω).toReal * (if ¬ retained ω c then (1 : ℝ) else 0)) ≤ ε) :
    (∑ ω : Ω, (μ ω).toReal * (violationCount I (output ω) : ℝ)) ≤
      ε * I.constraints.card := by
  unfold violationCount
  have heq := sum_violations I.constraints
    (fun ω c => ¬ c.Satisfied (output ω)) (fun ω => (μ ω).toReal)
  have hbound : ∀ c ∈ I.constraints,
      (∑ ω : Ω, (μ ω).toReal * (if ¬ c.Satisfied (output ω) then (1 : ℝ) else 0)) ≤ ε := by
    intro c hc
    calc
      _ ≤ ∑ ω : Ω, (μ ω).toReal * (if ¬ retained ω c then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro ω hω
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        by_cases hr : retained ω c
        · have hh := hsatisfy ω c hc hr
          simp [hr, hh]
        · simp only [hr, not_false_eq_true, if_true]
          split_ifs <;> norm_num
      _ ≤ ε := homit c hc
  have hb := sum_bounded I.constraints
    (fun c => ∑ ω : Ω, (μ ω).toReal *
      (if ¬ c.Satisfied (output ω) then (1 : ℝ) else 0)) ε hbound
  exact heq.le.trans hb

