-- Prove2me | solution 1 for SQMeanEstimation.lemma_3_16
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:56:27.065078+00:00
-- url     : https://prove2.me/submissions/97561f8c-66ca-4902-9d48-4cf8642295b1

import Mathlib
import Definitions.Def_SQMeanEstimation_vstatTol
import Definitions.Def_SQMeanEstimation_zeroSmall
import Definitions.Def_SQMeanEstimation_lowPart
import Definitions.Def_SQMeanEstimation_highPart

namespace Aux_SQMeanEstimation_lemma_3_16

theorem coord (q n x y : ℝ) (hq1 : 1 < q) (hn : 0 < n) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy : |y - x| ≤ max (1 / n) (Real.sqrt (x * (1 - x) / n))) :
    |x - (if 2 / n ≤ |y| then y else 0)| ^ q ≤
      |(if x < 4 / n then x else 0)| ^ q +
        n ^ (-q / 2) * |(if 1 / n ≤ x then x else 0)| ^ (q / 2) := by
  have ha : 0 < 1 / n := by positivity
  have h2 : 2 / n = 2 * (1 / n) := by ring
  have h4 : 4 / n = 4 * (1 / n) := by ring
  have hxn : x / n = x * (1 / n) := by ring
  obtain ⟨S, hS⟩ : ∃ S, S = Real.sqrt (x / n) := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact Real.sqrt_nonneg _
  have hS2 : S ^ 2 = x * (1 / n) := by
    rw [hS, Real.sq_sqrt (show (0 : ℝ) ≤ x / n by positivity), hxn]
  have hsq : Real.sqrt (x * (1 - x) / n) ≤ S := by
    rw [hS]
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ hn.le
    nlinarith
  have hy' : |y - x| ≤ max (1 / n) S := le_trans hy (max_le_max le_rfl hsq)
  have hnonneg1 : ∀ z : ℝ, 0 ≤ |z| ^ q := fun z => Real.rpow_nonneg (abs_nonneg z) q
  have hnonneg2 : ∀ z : ℝ, 0 ≤ n ^ (-q / 2) * |z| ^ (q / 2) :=
    fun z => mul_nonneg (Real.rpow_nonneg hn.le _) (Real.rpow_nonneg (abs_nonneg z) _)
  by_cases hyb : 2 / n ≤ |y|
  · rw [if_pos hyb]
    by_cases hx : 1 / n ≤ x
    · rw [if_pos hx, abs_of_nonneg hx0]
      have h1S : 1 / n ≤ S := by
        rw [hS]
        apply Real.le_sqrt_of_sq_le
        rw [hxn]
        nlinarith [mul_le_mul_of_nonneg_right hx ha.le]
      have hyS : |x - y| ≤ S := by
        rw [abs_sub_comm]
        exact le_trans hy' (max_le h1S le_rfl)
      have hpow : |x - y| ^ q ≤ S ^ q := Real.rpow_le_rpow (abs_nonneg _) hyS (by linarith)
      have hSq : S ^ q = n ^ (-q / 2) * x ^ (q / 2) := by
        rw [hS, Real.sqrt_eq_rpow, ← Real.rpow_mul (show (0 : ℝ) ≤ x / n by positivity),
          Real.div_rpow hx0 hn.le, show -q / 2 = -(q / 2) by ring, Real.rpow_neg hn.le,
          show 1 / (2 : ℝ) * q = q / 2 by ring]
        ring
      have := hnonneg1 (if x < 4 / n then x else 0)
      linarith
    · exfalso
      push_neg at hx
      have hSlt : S < 1 / n := by
        rw [hS, Real.sqrt_lt' ha, hxn]
        nlinarith [mul_lt_mul_of_pos_right hx ha]
      have hyx : |y - x| ≤ 1 / n := le_trans hy' (max_le le_rfl hSlt.le)
      have htri : |y| ≤ |y - x| + |x| := by
        have := abs_add_le (y - x) x
        simpa using this
      rw [abs_of_nonneg hx0] at htri
      linarith
  · rw [if_neg hyb, sub_zero]
    push_neg at hyb
    by_cases hx4 : x < 4 / n
    · rw [if_pos hx4]
      have := hnonneg2 (if 1 / n ≤ x then x else 0)
      linarith
    · exfalso
      push_neg at hx4
      have hyx : x - 2 / n < |y - x| := by
        have e1 : y ≤ |y| := le_abs_self y
        have e2 : x - y ≤ |y - x| := by
          rw [abs_sub_comm]
          exact le_abs_self _
        linarith
      rcases le_max_iff.mp hy' with h | h
      · linarith
      · have hxS : x / 2 < S := by linarith
        have hx2 : 0 ≤ x / 2 := by linarith
        have hm := mul_self_lt_mul_self hx2 hxS
        have hS2' : S * S = x * (1 / n) := by rw [← hS2]; ring
        nlinarith [mul_le_mul_of_nonneg_left hx4 hx0]

end Aux_SQMeanEstimation_lemma_3_16

open SQMeanEstimation in
theorem solution {d : ℕ} (q n : ℝ) (hq1 : 1 < q) (hq2 : q < 2) (hn : 0 < n)
    (u v' : Fin d → ℝ) (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1)
    (hv' : ∀ i, |v' i - u i| ≤ vstatTol n (u i)) :
    ∑ i, |u i - zeroSmall n v' i| ^ q ≤
      ∑ i, |lowPart n u i| ^ q + n ^ (-q / 2) * ∑ i, |highPart n u i| ^ (q / 2) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hvi := hv' i
  unfold vstatTol at hvi
  unfold zeroSmall lowPart highPart
  exact Aux_SQMeanEstimation_lemma_3_16.coord q n (u i) (v' i) hq1 hn (hu0 i) (hu1 i) hvi
