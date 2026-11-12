-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P63.classical_weighted_testing
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T19:18:02.094931+00:00
-- url     : https://prove2.me/submissions/1769a2c1-f522-4f3d-9e05-16490c8d5096

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P63

open Filter Topology

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {K : Type*} [Fintype K] [Nonempty K]
    (p q weight : K → ℝ) (hp : (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ (∑ i, q i) = 1)
    (hweight : ∀ i, weight i ∈ Set.Icc (0 : ℝ) 1) (mu : ℝ) :
    (∑ i, weight i * (p i - (2 : ℝ) ^ mu * q i)) ≤
      ∑ i, if (2 : ℝ) ^ mu * q i ≤ p i then p i else 0 := by
  apply Finset.sum_le_sum
  intro i _
  have hc : 0 < (2 : ℝ) ^ mu := Real.rpow_pos_of_pos (by norm_num) mu
  have hw := hweight i
  have hqi := hq.1 i
  have hcq : 0 ≤ (2 : ℝ) ^ mu * q i := mul_nonneg hc.le hqi
  split_ifs with h
  · have h1 : 0 ≤ p i - (2 : ℝ) ^ mu * q i := sub_nonneg.mpr h
    nlinarith [hw.1, hw.2, mul_le_mul_of_nonneg_right hw.2 h1]
  · have h1 : p i - (2 : ℝ) ^ mu * q i ≤ 0 := by
      push_neg at h
      linarith
    nlinarith [hw.1, mul_nonneg hw.1 (neg_nonneg.mpr h1)]
