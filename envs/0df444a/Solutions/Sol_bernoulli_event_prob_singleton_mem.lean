-- Prove2me | solution 1 for bernoulli_event_prob_singleton_mem
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-26T04:05:01.689706+00:00
-- url     : https://prove2.me/submissions/a9f4256a-5b41-40a0-abd9-5a5fb16549f0

import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

open MatrixCompletion
open scoped Classical BigOperators

private theorem sum_powerset_bernoulli_weight_eq_one
    {α : Type} [DecidableEq α] (s : Finset α) (p : ℝ) :
    (∑ Ω ∈ s.powerset, p ^ Ω.card * (1 - p) ^ (s.card - Ω.card)) = 1 := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    rw [Finset.sum_powerset_insert ha]
    have hleft :
        (∑ Ω ∈ s.powerset,
            p ^ Ω.card * (1 - p) ^ ((insert a s).card - Ω.card)) =
          (1 - p) * ∑ Ω ∈ s.powerset,
            p ^ Ω.card * (1 - p) ^ (s.card - Ω.card) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro Ω hΩ
      have hΩsub : Ω ⊆ s := Finset.mem_powerset.mp hΩ
      have hcardΩ : Ω.card ≤ s.card := Finset.card_le_card hΩsub
      have hcard :
          (insert a s).card - Ω.card = (s.card - Ω.card) + 1 := by
        rw [Finset.card_insert_of_notMem ha]
        omega
      rw [hcard, pow_succ]
      ring
    have hright :
        (∑ Ω ∈ s.powerset,
            p ^ (insert a Ω).card * (1 - p) ^ ((insert a s).card - (insert a Ω).card)) =
          p * ∑ Ω ∈ s.powerset,
            p ^ Ω.card * (1 - p) ^ (s.card - Ω.card) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro Ω hΩ
      have hΩsub : Ω ⊆ s := Finset.mem_powerset.mp hΩ
      have haΩ : a ∉ Ω := fun h => ha (hΩsub h)
      have hcard_insert_Ω : (insert a Ω).card = Ω.card + 1 :=
        Finset.card_insert_of_notMem haΩ
      have hcard :
          (insert a s).card - (insert a Ω).card = s.card - Ω.card := by
        rw [Finset.card_insert_of_notMem ha, hcard_insert_Ω]
        omega
      have hcard' : (insert a s).card - (Ω.card + 1) = s.card - Ω.card := by
        rw [← hcard_insert_Ω]
        exact hcard
      rw [hcard_insert_Ω, hcard', pow_succ]
      ring_nf
    rw [hleft, hright, ih]
    ring

private theorem sum_univ_bernoulli_mem_weight_eq
    {α : Type} [Fintype α] [DecidableEq α] (p : ℝ) (x : α) :
    (∑ Ω : Finset α,
        if x ∈ Ω then p ^ Ω.card * (1 - p) ^ (Fintype.card α - Ω.card) else 0) = p := by
  classical
  let s : Finset α := (Finset.univ : Finset α).erase x
  have hxs : x ∉ s := by simp [s]
  have huniv : insert x s = (Finset.univ : Finset α) := by
    ext y
    by_cases hy : y = x
    · simp [s, hy]
    · simp [s]
  have hsum_as_powerset :
      (∑ Ω : Finset α,
          if x ∈ Ω then p ^ Ω.card * (1 - p) ^ (Fintype.card α - Ω.card) else 0) =
        ∑ Ω ∈ (insert x s).powerset,
          if x ∈ Ω then p ^ Ω.card * (1 - p) ^ ((insert x s).card - Ω.card) else 0 := by
    rw [huniv]
    simp [Finset.powerset_univ]
  rw [hsum_as_powerset]
  rw [Finset.sum_powerset_insert hxs]
  have hfirst_zero :
      (∑ Ω ∈ s.powerset,
          if x ∈ Ω then p ^ Ω.card * (1 - p) ^ ((insert x s).card - Ω.card) else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro Ω hΩ
    have hΩsub : Ω ⊆ s := Finset.mem_powerset.mp hΩ
    have hxΩ : x ∉ Ω := fun hx => hxs (hΩsub hx)
    simp [hxΩ]
  have hsecond :
      (∑ Ω ∈ s.powerset,
          if x ∈ insert x Ω then
            p ^ (insert x Ω).card * (1 - p) ^ ((insert x s).card - (insert x Ω).card)
          else 0) =
        p * ∑ Ω ∈ s.powerset, p ^ Ω.card * (1 - p) ^ (s.card - Ω.card) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro Ω hΩ
    have hΩsub : Ω ⊆ s := Finset.mem_powerset.mp hΩ
    have hxΩ : x ∉ Ω := fun hx => hxs (hΩsub hx)
    have hcard_insert_Ω : (insert x Ω).card = Ω.card + 1 :=
      Finset.card_insert_of_notMem hxΩ
    have hcard :
        (insert x s).card - (insert x Ω).card = s.card - Ω.card := by
      rw [Finset.card_insert_of_notMem hxs, hcard_insert_Ω]
      omega
    have hcard' : (insert x s).card - (Ω.card + 1) = s.card - Ω.card := by
      rw [← hcard_insert_Ω]
      exact hcard
    simp [hcard_insert_Ω, hcard', pow_succ]
    ring_nf
  rw [hfirst_zero, zero_add, hsecond, sum_powerset_bernoulli_weight_eq_one]
  ring

theorem solution
    {n₁ n₂ : ℕ} (p : ℝ) (x : Fin n₁ × Fin n₂) :
    bernoulliEventProb p (fun Ω : Finset (Fin n₁ × Fin n₂) => x ∈ Ω) = p := by
  classical
  unfold bernoulliEventProb bernoulliObservationWeight
  simpa using
    (sum_univ_bernoulli_mem_weight_eq (α := Fin n₁ × Fin n₂) p x)
