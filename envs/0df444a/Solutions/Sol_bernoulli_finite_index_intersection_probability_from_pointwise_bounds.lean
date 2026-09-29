-- Prove2me | solution 1 for bernoulli_finite_index_intersection_probability_from_pointwise_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-21T21:21:04.651638+00:00
-- url     : https://prove2.me/submissions/8a3514a6-8280-4325-8fd2-3ed56ec7f158

import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion
open Finset
open scoped Classical BigOperators

universe u

theorem solution
    {ι : Type u} [Fintype ι] [DecidableEq ι] {n₁ n₂ : ℕ}
    (p c failureScale : ℝ)
    (Event : ι → Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 →
    (∀ i : ι, bernoulliEventProb p (Event i) ≥ 1 - c * failureScale) →
    bernoulliEventProb p (fun Omega => ∀ i : ι, Event i Omega) ≥
      1 - (((Fintype.card ι : ℝ) * c) * failureScale) := by
  intro hp0 hp1 hpt
  have hWnn : ∀ Ω : Finset (Fin n₁ × Fin n₂), 0 ≤ bernoulliObservationWeight p Ω := by
    intro Ω
    unfold bernoulliObservationWeight
    exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  -- total probability is 1
  have total : (∑ Ω : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Ω) = 1 := by
    unfold bernoulliObservationWeight
    have key : (∏ _c : Fin n₁ × Fin n₂, (p + (1 - p)))
        = ∑ Ω : Finset (Fin n₁ × Fin n₂),
            (∏ _c ∈ Ω, p) * ∏ _c ∈ univ \ Ω, (1 - p) := by
      rw [Finset.prod_add, Finset.powerset_univ]
    have hone : (∏ _c : Fin n₁ × Fin n₂, (p + (1 - p))) = 1 := by
      rw [Finset.prod_congr rfl (fun c _ => show p + (1 - p) = 1 by ring), Finset.prod_const_one]
    have hsum : (∑ Ω : Finset (Fin n₁ × Fin n₂),
          p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card))
        = ∑ Ω : Finset (Fin n₁ × Fin n₂), (∏ _c ∈ Ω, p) * ∏ _c ∈ univ \ Ω, (1 - p) := by
      apply Finset.sum_congr rfl
      intro Ω _
      rw [Finset.prod_const, Finset.prod_const, ← Finset.compl_eq_univ_sdiff, Finset.card_compl]
    rw [hsum, ← key]; exact hone
  -- complement identity
  have hcompl : ∀ (E : Finset (Fin n₁ × Fin n₂) → Prop),
      1 - bernoulliEventProb p E
        = ∑ Ω : Finset (Fin n₁ × Fin n₂),
            (if E Ω then (0 : ℝ) else bernoulliObservationWeight p Ω) := by
    intro E
    unfold bernoulliEventProb
    rw [← total, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro Ω _
    by_cases h : E Ω <;> simp [h]
  -- per-Ω union bound on indicators
  have perΩ : ∀ Ω : Finset (Fin n₁ × Fin n₂),
      (if (∀ i, Event i Ω) then (0 : ℝ) else bernoulliObservationWeight p Ω)
        ≤ ∑ i : ι, (if Event i Ω then (0 : ℝ) else bernoulliObservationWeight p Ω) := by
    intro Ω
    by_cases h : ∀ i, Event i Ω
    · rw [if_pos h]
      apply Finset.sum_nonneg
      intro i _
      split_ifs with hi
      · exact le_rfl
      · exact hWnn Ω
    · rw [if_neg h]
      obtain ⟨i₀, hi₀⟩ := not_forall.mp h
      have hnn : ∀ i ∈ (univ : Finset ι),
          0 ≤ (if Event i Ω then (0 : ℝ) else bernoulliObservationWeight p Ω) := by
        intro i _; split_ifs with hi
        · exact le_rfl
        · exact hWnn Ω
      have hle := Finset.single_le_sum hnn (mem_univ i₀)
      rwa [if_neg hi₀] at hle
  -- assemble the bound on the directly-written form
  have hsum : (∑ Ω : Finset (Fin n₁ × Fin n₂),
        (if (∀ i, Event i Ω) then (0 : ℝ) else bernoulliObservationWeight p Ω))
      ≤ (Fintype.card ι : ℝ) * c * failureScale := by
    calc (∑ Ω : Finset (Fin n₁ × Fin n₂),
            (if (∀ i, Event i Ω) then (0 : ℝ) else bernoulliObservationWeight p Ω))
        ≤ ∑ Ω : Finset (Fin n₁ × Fin n₂), ∑ i : ι,
            (if Event i Ω then (0 : ℝ) else bernoulliObservationWeight p Ω) :=
          Finset.sum_le_sum (fun Ω _ => perΩ Ω)
      _ = ∑ i : ι, ∑ Ω : Finset (Fin n₁ × Fin n₂),
            (if Event i Ω then (0 : ℝ) else bernoulliObservationWeight p Ω) := Finset.sum_comm
      _ = ∑ i : ι, (1 - bernoulliEventProb p (Event i)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hcompl (Event i)]
      _ ≤ ∑ _i : ι, c * failureScale := by
          apply Finset.sum_le_sum
          intro i _
          linarith [hpt i]
      _ = (Fintype.card ι : ℝ) * c * failureScale := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  -- bridge to the goal (Decidable-instance-agnostic)
  have main : 1 - bernoulliEventProb p (fun Ω => ∀ i, Event i Ω)
      ≤ (Fintype.card ι : ℝ) * c * failureScale := by
    rw [hcompl]
    refine le_of_eq_of_le ?_ hsum
    apply Finset.sum_congr rfl
    intro Ω _
    congr 1
  linarith [main]
