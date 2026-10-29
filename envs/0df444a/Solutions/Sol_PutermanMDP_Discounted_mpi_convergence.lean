-- Prove2me | solution 1 for PutermanMDP.Discounted.mpi_convergence
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T05:38:42.580986+00:00
-- url     : https://prove2.me/submissions/cb97e444-4391-47a3-a54f-e38bb64a9909

import Mathlib
import Definitions.Def_PutermanMDP_Discounted_Operators

open Filter Topology

namespace S226M_1919576e

open PutermanMDP.Discounted

noncomputable def M : Model Unit (fun _ => Unit) where
  reward := fun _ _ => 0
  reward_measurable := fun _ => measurable_const
  trans := fun _ _ _ => 1
  trans_nonneg := fun _ _ _ => zero_le_one
  trans_sum := fun _ _ => by simpa using (hasSum_fintype (fun _ : Unit => (1 : ℝ)))
  trans_measurable := fun _ _ => measurable_const
  bound := 0
  bound_nonneg := le_rfl
  reward_bounded := fun _ _ => by simp
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := zero_lt_one

lemma bellman_zero (v : Unit → ℝ) : bellman M v = fun _ => 0 := by
  funext s
  simp [bellman, M]

lemma policyOperator_zero (d : DecisionRule (fun _ : Unit => Unit)) (v : Unit → ℝ) :
    policyOperator M d v = fun _ => 0 := by
  funext s
  simp [policyOperator, M]

lemma hmax : MaxAttained M := by
  intro v _
  refine ⟨fun _ => (), ?_⟩
  unfold Greedy
  rw [bellman_zero, policyOperator_zero]

lemma hrun : MPIRun M (fun _ => 0) (fun _ _ => 0) (fun _ _ => ()) := by
  intro n
  refine ⟨?_, fun _ _ _ => rfl, ?_⟩
  · unfold Greedy; rw [bellman_zero, policyOperator_zero]
  · simp only [zero_add, Function.iterate_one]
    rw [policyOperator_zero]

lemma hv : VB M (fun _ => 0) := by
  refine ⟨⟨0, fun _ => by simp⟩, fun s => ?_⟩
  simp [PutermanMDP.Discounted.residual, bellman_zero]

lemma not_stop (ε : ℝ) (hε : 0 < ε) (v : Unit → ℝ) : ¬ Stop M ε v := by
  rintro ⟨t, ht, _⟩
  simp [M] at ht
  linarith

end S226M_1919576e

open Filter Topology in
open PutermanMDP.Discounted in
theorem solution : ¬ (∀ {S : Type} [Countable S] [Nonempty S] {A : S → Type}
    [∀ s, MeasurableSpace (A s)] [∀ s, StandardBorelSpace (A s)]
    [∀ s, Nonempty (A s)] (M : Model S A)
    (hmax : MaxAttained M) (m : ℕ → ℕ) (v : ℕ → S → ℝ)
    (d : ℕ → DecisionRule A) (hrun : MPIRun M m v d) (hv : VB M (v 0))
    (ε : ℝ) (hε : 0 < ε),
    ((∀ n s, v n s ≤ v (n + 1) s) ∧
      Tendsto (fun n => supNorm (v n - optimalValue M)) atTop (𝓝 0)) ∧
    (∃ N : ℕ, Stop M ε (v N) ∧ (∀ n < N, ¬ Stop M ε (v n)) ∧
      EpsilonOptimal M ε (stationary (d N)))) := by
  intro H
  obtain ⟨_, N, hN, _⟩ := H S226M_1919576e.M S226M_1919576e.hmax (fun _ => 0) (fun _ _ => 0)
    (fun _ _ => ()) S226M_1919576e.hrun S226M_1919576e.hv 1 one_pos
  exact S226M_1919576e.not_stop 1 one_pos _ hN
