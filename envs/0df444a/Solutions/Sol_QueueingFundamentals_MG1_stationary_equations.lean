-- Prove2me | solution 1 for QueueingFundamentals.MG1.stationary_equations
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:02:30.83967+00:00
-- url     : https://prove2.me/submissions/a79179c9-4807-4205-a264-dc46110e624d

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_embeddedChain

set_option autoImplicit false

open QueueingFundamentals.MG1 in
theorem cf619ccd_colsum (lam : ℝ) (B : MeasureTheory.Measure ℝ) (π : ℕ → ℝ) (j : ℕ) :
    HasSum (fun i => π i * transitionMatrix lam B i j)
      (π 0 * arrivalProb lam B j +
        ∑ i ∈ Finset.Icc 1 (j + 1), π i * arrivalProb lam B (j + 1 - i)) := by
  have hsupp : ∀ i ∉ Finset.range (j + 2), π i * transitionMatrix lam B i j = 0 := by
    intro i hi
    simp only [Finset.mem_range, not_lt] at hi
    have h1 : i ≠ 0 := by omega
    have h2 : ¬ i ≤ j + 1 := by omega
    simp [transitionMatrix, h1, h2]
  have h : HasSum (fun i => π i * transitionMatrix lam B i j)
      (∑ i ∈ Finset.range (j + 2), π i * transitionMatrix lam B i j) :=
    hasSum_sum_of_ne_finset_zero hsupp
  have e : ∑ i ∈ Finset.Icc 1 (j + 1), π i * arrivalProb lam B (j + 1 - i) =
      ∑ k ∈ Finset.range (j + 1), π (k + 1) * transitionMatrix lam B (k + 1) j := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr (by simp)
    intro k hk
    simp only [Finset.mem_range] at hk
    have h3 : k + 1 ≠ 0 := by omega
    have h4 : k + 1 ≤ j + 1 := by omega
    rw [add_comm 1 k, transitionMatrix, if_neg h3, if_pos h4]
  have e0 : transitionMatrix lam B 0 j = arrivalProb lam B j := by simp [transitionMatrix]
  convert h using 1
  rw [Finset.sum_range_succ', e, e0]
  ring

open QueueingFundamentals.MG1 MeasureTheory in
theorem solution (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0)
    (π : ℕ → ℝ) (hπ0 : ∀ n, 0 ≤ π n) (hπ1 : HasSum π 1) :
    IsStationaryDist (transitionMatrix lam B) π ↔
      ∀ i : ℕ, π i = π 0 * arrivalProb lam B i +
        ∑ j ∈ Finset.Icc 1 (i + 1), π j * arrivalProb lam B (i + 1 - j) := by
  constructor
  · rintro ⟨_, _, h⟩ i
    exact (h i).unique (cf619ccd_colsum lam B π i)
  · intro h
    refine ⟨hπ0, hπ1, fun j => ?_⟩
    rw [h j]
    exact cf619ccd_colsum lam B π j
