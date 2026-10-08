-- Prove2me | solution 1 for QueueingFundamentals.MG1.pgf_stationary
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T17:07:30.148338+00:00
-- url     : https://prove2.me/submissions/19d2855f-8291-416a-aae5-b21cfb650199

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_embeddedChain

set_option autoImplicit false

open MeasureTheory Finset

namespace PgfStatAux
open QueueingFundamentals.MG1

lemma k_nonneg (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) (hB : B (Set.Iio 0) = 0) (i : ℕ) :
    0 ≤ arrivalProb lam B i := by
  unfold arrivalProb
  apply integral_nonneg_of_ae
  have h := (measure_eq_zero_iff_ae_notMem.mp hB)
  filter_upwards [h] with t ht
  have : 0 ≤ t := by simpa using ht
  simp only [Pi.zero_apply]
  positivity

lemma P_nonneg (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) (hB : B (Set.Iio 0) = 0) (i j : ℕ) :
    0 ≤ transitionMatrix lam B i j := by
  unfold transitionMatrix
  split_ifs
  · exact k_nonneg lam hlam B hB _
  · exact k_nonneg lam hlam B hB _
  · exact le_refl 0

lemma row (lam : ℝ) (B : Measure ℝ) (π : ℕ → ℝ)
    (hπ : IsStationaryDist (transitionMatrix lam B) π) (j : ℕ) :
    π j = π 0 * arrivalProb lam B j
      + ∑ i ∈ range (j+1), π (i+1) * arrivalProb lam B (j - i) := by
  have h1 : HasSum (fun i => π i * transitionMatrix lam B i j)
      (∑ i ∈ range (j+2), π i * transitionMatrix lam B i j) := by
    apply hasSum_sum_of_ne_finset_zero
    intro i hi
    simp only [mem_range, not_lt] at hi
    have h0 : i ≠ 0 := by omega
    have h2 : ¬ i ≤ j + 1 := by omega
    simp [transitionMatrix, h0, h2]
  rw [(hπ.2.2 j).unique h1, sum_range_succ', add_comm]
  refine congrArg₂ (· + ·) ?_ ?_
  · simp [transitionMatrix]
  · apply sum_congr rfl
    intro i hi
    simp only [mem_range] at hi
    have h2 : i + 1 ≤ j + 1 := by omega
    have e : j + 1 - (i + 1) = j - i := by omega
    simp [transitionMatrix, h2, e]

lemma k_summable (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) (hB : B (Set.Iio 0) = 0)
    (π : ℕ → ℝ) (hπ : IsStationaryDist (transitionMatrix lam B) π) :
    Summable (arrivalProb lam B) := by
  obtain ⟨i0, hi0⟩ : ∃ i, π i ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : HasSum π 0 := by
      have : π = 0 := funext h
      rw [this]; exact hasSum_zero
    exact one_ne_zero (hπ.2.1.unique h0)
  have hpos : 0 < π i0 := lt_of_le_of_ne (hπ.1 i0) (Ne.symm hi0)
  have hsum := hπ.2.1.summable
  have key : ∀ j, π i0 * transitionMatrix lam B i0 j ≤ π j := fun j =>
    le_hasSum (hπ.2.2 j) i0 (fun i _ => mul_nonneg (hπ.1 i) (P_nonneg lam hlam B hB i j))
  rcases Nat.eq_zero_or_pos i0 with h | h
  · subst h
    refine Summable.of_nonneg_of_le (fun m => k_nonneg lam hlam B hB m) (fun m => ?_)
      (hsum.div_const (π 0))
    rw [le_div_iff₀ hpos]
    have := key m
    simp only [transitionMatrix, if_true] at this
    linarith
  · obtain ⟨n, rfl⟩ : ∃ n, i0 = n + 1 := ⟨i0 - 1, by omega⟩
    refine Summable.of_nonneg_of_le (fun m => k_nonneg lam hlam B hB m) (fun m => ?_)
      (((summable_nat_add_iff n).mpr hsum).div_const (π (n+1)))
    rw [le_div_iff₀ hpos]
    have := key (m + n)
    have e : n + 1 ≤ m + n + 1 := by omega
    have e2 : m + n + 1 - (n + 1) = m := by omega
    simp only [transitionMatrix, Nat.add_one_ne_zero, if_false, e, if_true, e2] at this
    linarith

lemma algebra (P K p0 z : ℂ) (a b : ℕ → ℂ) (hP : HasSum a P) (hK : HasSum b K)
    (ha : Summable fun i => ‖a i‖) (hb : Summable fun i => ‖b i‖) (ha0 : a 0 = p0)
    (hrow : ∀ j, z * a j = p0 * z * b j + ∑ i ∈ range (j+1), a (i+1) * b (j - i)) :
    z * P = p0 * z * K + (P - p0) * K := by
  have ha' : Summable fun i => ‖a (i+1)‖ := (summable_nat_add_iff 1).mpr ha
  have hP' : HasSum (fun i => a (i+1)) (P - p0) := by
    have := (hasSum_nat_add_iff' 1).mpr hP
    simpa [ha0] using this
  have hC := hasSum_sum_range_mul_of_summable_norm ha' hb
  rw [hP'.tsum_eq, hK.tsum_eq] at hC
  have h1 : HasSum (fun j => z * a j) (z * P) := hP.mul_left z
  have h2 : HasSum (fun j => p0 * z * b j + ∑ i ∈ range (j+1), a (i+1) * b (j - i))
      (p0 * z * K + (P - p0) * K) := (hK.mul_left (p0 * z)).add hC
  have hf : (fun j => z * a j) = (fun j => p0 * z * b j + ∑ i ∈ range (j+1), a (i+1) * b (j - i)) :=
    funext hrow
  rw [hf] at h1
  exact h1.unique h2

end PgfStatAux

open QueueingFundamentals.MG1 MeasureTheory in
theorem solution (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0)
    (π : ℕ → ℝ) (hπ : IsStationaryDist (transitionMatrix lam B) π)
    (z : ℂ) (hz : ‖z‖ ≤ 1) (hK : pgf (arrivalProb lam B) z ≠ z) :
    pgf π z = (π 0 : ℂ) * (1 - z) * pgf (arrivalProb lam B) z /
      (pgf (arrivalProb lam B) z - z) := by
  have hknn := PgfStatAux.k_nonneg lam hlam B hB
  have hks := PgfStatAux.k_summable lam hlam B hB π hπ
  have hπs := hπ.2.1.summable
  have hzn : ∀ i : ℕ, ‖z ^ i‖ ≤ 1 := fun i => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz
  have ha : Summable fun i => ‖(π i : ℂ) * z ^ i‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) hπs
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hπ.1 i)]
    exact mul_le_of_le_one_right (hπ.1 i) (hzn i)
  have hb : Summable fun i => ‖(arrivalProb lam B i : ℂ) * z ^ i‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) hks
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hknn i)]
    exact mul_le_of_le_one_right (hknn i) (hzn i)
  have hP : HasSum (fun i => (π i : ℂ) * z ^ i) (pgf π z) := ha.of_norm.hasSum
  have hKs : HasSum (fun i => (arrivalProb lam B i : ℂ) * z ^ i) (pgf (arrivalProb lam B) z) :=
    hb.of_norm.hasSum
  have E := PgfStatAux.algebra (pgf π z) (pgf (arrivalProb lam B) z) (π 0 : ℂ) z
    (fun i => (π i : ℂ) * z ^ i) (fun i => (arrivalProb lam B i : ℂ) * z ^ i) hP hKs ha hb
    (by simp) (by
      intro j
      have hsum_eq : ∑ i ∈ range (j+1), ((π (i+1) : ℂ) * z ^ (i+1)) *
          ((arrivalProb lam B (j - i) : ℂ) * z ^ (j - i)) =
          z ^ (j+1) * ∑ i ∈ range (j+1), ((π (i+1) : ℂ) * (arrivalProb lam B (j - i) : ℂ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [mem_range] at hi
        have : z ^ (j+1) = z ^ (i+1) * z ^ (j - i) := by
          rw [← pow_add]; congr 1; omega
        rw [this]; ring
      rw [hsum_eq]
      have h := PgfStatAux.row lam B π hπ j
      have hc : (π j : ℂ) = (π 0 : ℂ) * (arrivalProb lam B j : ℂ) +
          ∑ i ∈ range (j+1), ((π (i+1) : ℂ) * (arrivalProb lam B (j - i) : ℂ)) := by
        rw [h]; push_cast; ring
      rw [hc]; ring)
  rw [eq_div_iff (sub_ne_zero.mpr hK)]
  linear_combination (-1 : ℂ) * E
