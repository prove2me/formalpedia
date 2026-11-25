-- Prove2me | solution 1 for SimpleGraph.exists_dependentRandomChoice_of_card_edgeFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:03:15.73615+00:00
-- url     : https://prove2.me/submissions/32a9008b-f8c1-4f51-89ab-8336b6402430

module
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic.Rify
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_ProbabilisticMethod_DependentRandomChoice
public import Theorems.Thm_SimpleGraph_exists_dependentRandomChoice

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution [Nonempty V] {t r m a : ℕ} (hr : 1 ≤ r)
    (h : (a : ℝ) + (Fintype.card V).choose r * ((m : ℝ) / Fintype.card V) ^ t ≤
      Fintype.card V * ((2 * #G.edgeFinset : ℝ) / Fintype.card V / Fintype.card V) ^ t) :
    ∃ W : Finset V, a ≤ #W ∧ ∀ S ⊆ W, #S = r → m ≤ #{u | ∀ v ∈ S, G.Adj v u} := by
  refine G.exists_dependentRandomChoice (t := t) hr ?_
  set n := Fintype.card V
  have hn : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  -- power mean: `n (∑ deg / n) ^ t ≤ ∑ deg ^ t`
  have hpm : (n : ℝ) * ((2 * #G.edgeFinset : ℝ) / n) ^ t ≤ ∑ v, (G.degree v : ℝ) ^ t := by
    have hjensen := pow_sum_div_card_le_sum_pow (s := (univ : Finset V))
      (f := fun v => (G.degree v : ℝ)) (fun _ _ => by positivity) (t - 1)
    have hdeg : ∑ v, (G.degree v : ℝ) = 2 * #G.edgeFinset := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [n]
    rw [card_univ, hdeg, Nat.sub_add_cancel ht] at hjensen
    calc (n : ℝ) * ((2 * #G.edgeFinset : ℝ) / n) ^ t
        = (2 * #G.edgeFinset : ℝ) ^ t / (n : ℝ) ^ (t - 1) := by
          rw [div_pow, ← mul_div_assoc, mul_comm, mul_div_assoc,
            show (n : ℝ) ^ t = n ^ (t - 1) * n by rw [← pow_succ, Nat.sub_add_cancel ht]]
          field_simp
      _ ≤ _ := hjensen
  have hnt : (0 : ℝ) < (n : ℝ) ^ t := pow_pos hn t
  have key : ((a * n ^ t + n.choose r * m ^ t : ℕ) : ℝ) ≤ ∑ v, (G.degree v : ℝ) ^ t := by
    push_cast
    have : ((a : ℝ) + n.choose r * ((m : ℝ) / n) ^ t) * (n : ℝ) ^ t ≤
        (n * ((2 * #G.edgeFinset : ℝ) / n / n) ^ t) * (n : ℝ) ^ t :=
      mul_le_mul_of_nonneg_right h hnt.le
    have e1 : ((a : ℝ) + n.choose r * ((m : ℝ) / n) ^ t) * (n : ℝ) ^ t =
        a * n ^ t + n.choose r * m ^ t := by
      rw [div_pow]; field_simp
    have e2 : (n * ((2 * #G.edgeFinset : ℝ) / n / n) ^ t) * (n : ℝ) ^ t =
        n * ((2 * #G.edgeFinset : ℝ) / n) ^ t := by
      rw [mul_assoc, ← mul_pow, div_div, div_mul_eq_mul_div, mul_div_mul_right _ _ hn.ne']
    rw [e1, e2] at this
    exact this.trans hpm
  exact_mod_cast key
end SimpleGraph
