-- Prove2me | solution 1 for PoissonDepTrials.MixSqrt.cauchy_schwarz_4_10
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:30:55.016376+00:00
-- url     : https://prove2.me/submissions/3bb08b3a-8f9e-44e5-a0d9-1fa225bea72a

import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

theorem cs410_card_le (n m i : ℕ) :
    ((Finset.Icc 1 n).filter (fun j : ℕ => |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m)).card ≤ 2 * m + 1 := by
  have h := Finset.card_le_card_of_injOn (fun j : ℕ => (j : ℤ))
    (s := (Finset.Icc 1 n).filter (fun j : ℕ => |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m))
    (t := Finset.Icc ((i : ℤ) - m) ((i : ℤ) + m)) ?_ ?_
  · rw [Int.card_Icc] at h
    omega
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hj
    simp only [Finset.coe_Icc, Set.mem_Icc]
    have := abs_le.mp hj.2
    constructor <;> linarith [this.1, this.2]
  · intro a _ b _ hab
    simpa using hab

theorem cs410_real (n m : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m, f i * f j
      ≤ (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, f i ^ 2 := by
  set S : ℕ → Finset ℕ := fun i =>
    (Finset.Icc 1 n).filter (fun j : ℕ => |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m) with hS
  have hA : ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, f i ^ 2
      ≤ (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, f i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hc : (S i).card ≤ 2 * m + 1 := cs410_card_le n m i
    exact_mod_cast hc
  have hB : ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, f j ^ 2
      = ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, f i ^ 2 := by
    simp only [hS, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [abs_sub_comm]
  have hpt : ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, f i * f j
      ≤ ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, (f i ^ 2 + f j ^ 2) / 2 := by
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    nlinarith [sq_nonneg (f i - f j)]
  have hsplit : ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, (f i ^ 2 + f j ^ 2) / 2
      = (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, f i ^ 2
         + ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, f j ^ 2) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib, Finset.sum_div]
  show ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, f i * f j ≤ _
  linarith [hpt, hsplit, hA, hB]

open MeasureTheory ProbabilityTheory PoissonDepTrials.MixSqrt in
theorem solution (n m : ℕ) (p : ℕ → ℝ) :
    ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m, p i * p j
      ≤ (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, p i ^ 2 := by
  exact cs410_real n m p
