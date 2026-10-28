-- Prove2me | solution 1 for PersonalizedRM.RevenueGap.lemma_EC_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:24:33.494726+00:00
-- url     : https://prove2.me/submissions/1720e199-ca0e-4ba6-b874-6a555145b1fa

import Mathlib
import Definitions.Def_PersonalizedRM_RevenueGap_Model

open MeasureTheory ProbabilityTheory

theorem solution {ι : Type*} [Fintype ι] (q : ι → ℝ) (hq_pos : ∀ j, 0 < q j)
    (hq_sum : ∑ j, q j < 1) (m : ℝ) (hm : ∀ j, m ≤ q j) (u : ι → ℝ) :
    0 ≤ ∑ j, q j * u j ^ 2 - (∑ j, q j * u j) ^ 2 ∧
      m * (1 - ∑ j, q j) * ∑ j, u j ^ 2 ≤ ∑ j, q j * u j ^ 2 - (∑ j, q j * u j) ^ 2 := by
  have hCS : (∑ j, q j * u j) ^ 2 ≤ (∑ j, q j) * ∑ j, q j * u j ^ 2 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun j _ => (hq_pos j).le)
      (fun j _ => mul_nonneg (hq_pos j).le (sq_nonneg _)) (fun j _ => by ring_nf; exact le_rfl)
  have hA : 0 ≤ ∑ j, q j * u j ^ 2 :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hq_pos j).le (sq_nonneg _))
  have hQ : 0 < 1 - ∑ j, q j := by linarith
  have hlow : (1 - ∑ j, q j) * ∑ j, q j * u j ^ 2 ≤
      ∑ j, q j * u j ^ 2 - (∑ j, q j * u j) ^ 2 := by nlinarith
  refine ⟨le_trans (mul_nonneg hQ.le hA) hlow, ?_⟩
  have hmA : m * ∑ j, u j ^ 2 ≤ ∑ j, q j * u j ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hm j) (sq_nonneg _))
  have : (1 - ∑ j, q j) * (m * ∑ j, u j ^ 2) ≤ (1 - ∑ j, q j) * ∑ j, q j * u j ^ 2 :=
    mul_le_mul_of_nonneg_left hmA hQ.le
  nlinarith
