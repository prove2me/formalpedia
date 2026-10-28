-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P25.waitingDistribution
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T23:26:12.353905+00:00
-- url     : https://prove2.me/submissions/0236e59e-1cba-4cd2-81d4-797d37826ed8

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

open QAlgorithms.Papers.Independent.Gap48.P25
noncomputable section


open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)


namespace P25WaitH
open QAlgorithms.Papers.Independent.Gap48.P25 Finset

lemma S_succ (x : ℝ) (k : ℕ) : ∑ i ∈ range (k+1), geometricRound x i = 1 - (1-x)^k := by
  induction k with
  | zero => simp [geometricRound]
  | succ k ih =>
    rw [sum_range_succ, ih]; simp [geometricRound]; ring

lemma W_eq (x : ℝ) (m : ℕ) : twoLinkWaiting x m =
    (∑ i ∈ range (m+1), geometricRound x i)^2 - (∑ i ∈ range m, geometricRound x i)^2 := by
  unfold twoLinkWaiting
  rw [sq, sq, sum_mul_sum, sum_mul_sum, ← sum_product', ← sum_product']
  rw [← sum_filter]
  have h := sum_filter_add_sum_filter_not (range (m+1) ×ˢ range (m+1))
    (fun q : ℕ × ℕ => max q.1 q.2 = m) (fun q => geometricRound x q.1 * geometricRound x q.2)
  have hf : (range (m+1) ×ˢ range (m+1)).filter (fun q : ℕ × ℕ => ¬ max q.1 q.2 = m) =
      range m ×ˢ range m := by
    ext ⟨i, j⟩; simp only [mem_filter, mem_product, mem_range]; omega
  rw [hf, Finset.sum_product (range m) (range m)] at h
  linarith

lemma W_nonneg (x : ℝ) (hx : 0 < x ∧ x ≤ 1) (n : ℕ) : 0 ≤ twoLinkWaiting x n := by
  have hg : ∀ i, 0 ≤ geometricRound x i := by
    intro i; unfold geometricRound; split_ifs
    · exact le_refl _
    · exact mul_nonneg hx.1.le (pow_nonneg (by linarith [hx.2]) _)
  unfold twoLinkWaiting
  apply sum_nonneg; intro i _; apply sum_nonneg; intro j _
  split_ifs
  · exact mul_nonneg (hg i) (hg j)
  · exact le_refl _

end P25WaitH

/-- Footnote 75, PDF p.46: exact law and mean of two independent geometric
links. Includes x=1, excludes x=0 from the real expectation formula. -/
theorem solution (x : ℝ) (hx : 0 < x ∧ x ≤ 1) :
    (∀ n, 0 ≤ twoLinkWaiting x n) ∧ HasSum (twoLinkWaiting x) 1 ∧
    (∀ n : ℕ, 1 ≤ n → twoLinkWaiting x n = x*(1-x)^(n-1)*(2-(2-x)*(1-x)^(n-1))) ∧
    HasSum (fun n : ℕ => (n : ℝ)*twoLinkWaiting x n) (waitingMean x) ∧
    Tendsto (fun z : ℝ => z*waitingMean z) (nhdsWithin 0 (Set.Ioi 0)) (nhds (3/2)) := by
  have hx0 := hx.1
  have hx1 := hx.2
  set r := 1 - x with hr
  have hr0 : 0 ≤ r := by linarith
  have hr1 : r < 1 := by linarith
  have hW := P25WaitH.W_nonneg x hx
  have hform : ∀ k : ℕ, twoLinkWaiting x (k+1) = x*r^k*(2-(2-x)*r^k) := by
    intro k
    rw [P25WaitH.W_eq, P25WaitH.S_succ, P25WaitH.S_succ, pow_succ]; ring
  refine ⟨hW, ?_, fun n hn => ?_, ?_, ?_⟩
  · rw [hasSum_iff_tendsto_nat_of_nonneg hW]
    have hpart : ∀ N, ∑ i ∈ Finset.range N, twoLinkWaiting x i =
        (∑ i ∈ Finset.range N, geometricRound x i)^2 := by
      intro N
      rw [Finset.sum_congr rfl (fun i _ => P25WaitH.W_eq x i)]
      rw [Finset.sum_range_sub (fun k => (∑ i ∈ Finset.range k, geometricRound x i)^2) N]
      simp
    simp_rw [hpart]
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    simp_rw [P25WaitH.S_succ]
    have := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have h2 := ((tendsto_const_nhds (x := (1:ℝ))).sub this).pow 2
    simpa using h2
  · obtain ⟨k, rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
    rw [hform]; simp
  · rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
    have hnr : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
    have hs0 : 0 ≤ r^2 := by positivity
    have hs1 : r^2 < 1 := by nlinarith
    have hns : ‖r^2‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hs0]; exact hs1
    have A := hasSum_coe_mul_geometric_of_norm_lt_one hnr
    have B := hasSum_geometric_of_lt_one hr0 hr1
    have A2 := hasSum_coe_mul_geometric_of_norm_lt_one hns
    have B2 := hasSum_geometric_of_lt_one hs0 hs1
    have H := ((A.add B).mul_left (2*x)).sub ((A2.add B2).mul_left (x*(2-x)))
    convert H using 1
    · funext m
      rw [hform]; push_cast; rw [← pow_mul, mul_comm 2 m, pow_mul]; ring
    · have h2x : (2 - x) ≠ 0 := by linarith
      have e1 : 1 - r = x := by rw [hr]; ring
      have e2 : 1 - r^2 = x*(2-x) := by rw [hr]; ring
      rw [e1, e2]; unfold waitingMean; rw [hr]; field_simp; ring
  · have hc : Tendsto (fun z:ℝ => (3-2*z)/(2-z)) (nhds 0) (nhds (3/2)) := by
      have := ((tendsto_const_nhds (x:=(3:ℝ))).sub ((tendsto_id (x := nhds (0:ℝ))).const_mul 2)).div
        ((tendsto_const_nhds (x:=(2:ℝ))).sub (tendsto_id (x := nhds (0:ℝ)))) (by norm_num)
      rw [show (3:ℝ)/2 = (3-2*0)/(2-0) by norm_num]; exact this
    refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    unfold waitingMean
    rw [mul_div_assoc', mul_div_mul_left _ _ (ne_of_gt hz)]




