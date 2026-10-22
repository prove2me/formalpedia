-- Prove2me | solution 1 for WaitJudge.Convex.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T16:22:50.769183+00:00
-- url     : https://prove2.me/submissions/5fdb3621-3504-47c0-b9ab-d1205fc446bd

import Mathlib

open MeasureTheory

theorem solution (d M N : ℕ) (hdM : d ≤ M) (ε : ℕ → ℝ) (hε : ∀ k ≤ d, 0 ≤ ε k ∧ ε k ≤ 1)
    (μ : ℕ → MeasureTheory.Measure ℝ) [∀ k, MeasureTheory.IsFiniteMeasure (μ k)]
    (hmom : ∀ m ≤ M, ∑ k ∈ Finset.range (min m d + 1),
      (m.choose k : ℝ) * ∫ v in Set.Icc 0 1, (1 - v) ^ (m - k) ∂(μ k) = 1)
    (lam : ℕ → ℝ)
    (hlam : ∀ k ≤ d, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      (N.choose k : ℝ) * (1 - v) ^ (N - k) * Set.indicator (Set.Ioc (ε k) 1) 1 v ≤
        ∑ m ∈ Finset.Icc k M, lam m * (m.choose k : ℝ) * (1 - v) ^ (m - k)) :
    ∑ k ∈ Finset.range (d + 1), (N.choose k : ℝ) * ∫ v in Set.Ioc (ε k) 1, (1 - v) ^ (N - k) ∂(μ k) ≤
      ∑ m ∈ Finset.range (M + 1), lam m := by
  have hpolyint : ∀ k (p : ℕ), IntegrableOn (fun v : ℝ => (1 - v) ^ p) (Set.Icc 0 1) (μ k) :=
    fun k p => (by fun_prop : Continuous (fun v : ℝ => (1 - v) ^ p)).continuousOn.integrableOn_compact
      isCompact_Icc
  have step : ∀ k ∈ Finset.range (d + 1),
      (N.choose k : ℝ) * ∫ v in Set.Ioc (ε k) 1, (1 - v) ^ (N - k) ∂(μ k) ≤
        ∑ m ∈ Finset.Icc k M, lam m * ((m.choose k : ℝ) *
          ∫ v in Set.Icc 0 1, (1 - v) ^ (m - k) ∂(μ k)) := by
    intro k hk
    have hkd : k ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hsub : Set.Ioc (ε k) 1 ⊆ Set.Icc 0 1 := fun v hv =>
      ⟨le_trans (hε k hkd).1 hv.1.le, hv.2⟩
    have e1 : (N.choose k : ℝ) * ∫ v in Set.Ioc (ε k) 1, (1 - v) ^ (N - k) ∂(μ k) =
        ∫ v in Set.Icc 0 1, (N.choose k : ℝ) * (1 - v) ^ (N - k) *
          Set.indicator (Set.Ioc (ε k) 1) 1 v ∂(μ k) := by
      rw [← integral_const_mul]
      have : (fun v : ℝ => (N.choose k : ℝ) * (1 - v) ^ (N - k) *
          Set.indicator (Set.Ioc (ε k) 1) 1 v) =
          Set.indicator (Set.Ioc (ε k) 1) (fun v => (N.choose k : ℝ) * (1 - v) ^ (N - k)) := by
        funext v
        by_cases hv : v ∈ Set.Ioc (ε k) 1 <;> simp [hv]
      rw [this, setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.2 hsub]
    have e2 : ∫ v in Set.Icc 0 1, ∑ m ∈ Finset.Icc k M,
        lam m * (m.choose k : ℝ) * (1 - v) ^ (m - k) ∂(μ k) =
        ∑ m ∈ Finset.Icc k M, lam m * ((m.choose k : ℝ) *
          ∫ v in Set.Icc 0 1, (1 - v) ^ (m - k) ∂(μ k)) := by
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro m _
        rw [← integral_const_mul, ← integral_const_mul]
        congr 1; funext v; ring
      · intro m _
        exact ((hpolyint k (m - k)).const_mul _)
    rw [e1, ← e2]
    apply setIntegral_mono_on
    · have : (fun v : ℝ => (N.choose k : ℝ) * (1 - v) ^ (N - k) *
          Set.indicator (Set.Ioc (ε k) 1) 1 v) =
          Set.indicator (Set.Ioc (ε k) 1) (fun v => (N.choose k : ℝ) * (1 - v) ^ (N - k)) := by
        funext v
        by_cases hv : v ∈ Set.Ioc (ε k) 1 <;> simp [hv]
      rw [this]
      exact (((hpolyint k (N - k)).const_mul _).indicator measurableSet_Ioc)
    · exact integrable_finset_sum _ (fun m _ => by
        simpa [mul_assoc] using ((hpolyint k (m - k)).const_mul (lam m * (m.choose k : ℝ))))
    · exact measurableSet_Icc
    · intro v hv
      exact hlam k hkd v hv
  calc _ ≤ ∑ k ∈ Finset.range (d + 1), ∑ m ∈ Finset.Icc k M, lam m * ((m.choose k : ℝ) *
          ∫ v in Set.Icc 0 1, (1 - v) ^ (m - k) ∂(μ k)) := Finset.sum_le_sum step
    _ = ∑ m ∈ Finset.range (M + 1), ∑ k ∈ Finset.range (min m d + 1), lam m *
          ((m.choose k : ℝ) * ∫ v in Set.Icc 0 1, (1 - v) ^ (m - k) ∂(μ k)) := by
        apply Finset.sum_comm'
        intro k m
        simp only [Finset.mem_range, Finset.mem_Icc]
        omega
    _ = ∑ m ∈ Finset.range (M + 1), lam m := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [← Finset.mul_sum, hmom m (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)), mul_one]
