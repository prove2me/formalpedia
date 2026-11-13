-- Prove2me | solution 1 for StabilityDichotomies.Solvability.approximation_of_constraint_bounds
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T04:57:14.198001+00:00
-- url     : https://prove2.me/submissions/3d92c5f7-a051-494e-a1e4-b8237ee15443

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
    (Γ : Language) (A : Solver Γ) (ε : ℝ)
    (h : ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
      ∀ c ∈ I.constraints,
        (∑ x : V → Bool, (A V I x).toReal * (if ¬ c.Satisfied x then (1 : ℝ) else 0)) ≤ ε) :
    Approximates A ε := by
  intro V _ I hI
  unfold violationCount
  have heq := sum_violations I.constraints
    (fun (x : V → Bool) c => ¬ c.Satisfied x) (fun x => (A V I x).toReal)
  have hb := sum_bounded I.constraints
    (fun c => ∑ x : V → Bool, (A V I x).toReal * (if ¬ c.Satisfied x then 1 else 0)) ε
    (h V I hI)
  exact heq.le.trans hb

