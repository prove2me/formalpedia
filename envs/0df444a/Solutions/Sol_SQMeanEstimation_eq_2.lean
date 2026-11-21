-- Prove2me | solution 1 for SQMeanEstimation.eq_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:06:20.494387+00:00
-- url     : https://prove2.me/submissions/7d5de88d-55a1-44d3-a5b9-9c472be4fabb

import Mathlib
import Definitions.Def_SQMeanEstimation_lqNorm
import Definitions.Def_SQMeanEstimation_posPart
import Definitions.Def_SQMeanEstimation_ringPart

open MeasureTheory

namespace Aux_SQMeanEstimation_eq_2

open SQMeanEstimation

theorem coord_bound {d : ℕ} (q : ℝ) (hq1 : 1 < q) (j : ℕ) (w : Fin d → ℝ) (i : Fin d) :
    |ringPart j (SQMeanEstimation.posPart w) i| ≤ ((2 : ℝ) ^ (-(j : ℝ) - 1)) ^ (1 - q) * |w i| ^ q := by
  have hCpos : 0 < ((2 : ℝ) ^ (-(j : ℝ) - 1)) ^ (1 - q) :=
    Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _) _
  show |(if (2 : ℝ) ^ (-((j : ℝ) + 1)) < |SQMeanEstimation.posPart w i| ∧ |SQMeanEstimation.posPart w i| ≤ (2 : ℝ) ^ (-(j : ℝ))
      then SQMeanEstimation.posPart w i else 0)| ≤ ((2 : ℝ) ^ (-(j : ℝ) - 1)) ^ (1 - q) * |w i| ^ q
  split_ifs with hc
  · have ha : (0 : ℝ) < (2 : ℝ) ^ (-((j : ℝ) + 1)) := by positivity
    by_cases h0 : 0 ≤ w i
    · have hp : SQMeanEstimation.posPart w i = w i := by simp [SQMeanEstimation.posPart, h0]
      rw [hp] at hc ⊢
      have hwpos : 0 < |w i| := lt_trans ha hc.1
      have h1 : |w i| ^ (1 - q) ≤ ((2 : ℝ) ^ (-(j : ℝ) - 1)) ^ (1 - q) := by
        rw [show -(j : ℝ) - 1 = -((j : ℝ) + 1) by ring]
        exact Real.rpow_le_rpow_of_nonpos ha hc.1.le (by linarith)
      have h2 : |w i| = |w i| ^ (1 - q) * |w i| ^ q := by
        rw [← Real.rpow_add hwpos, show 1 - q + q = 1 by ring, Real.rpow_one]
      calc |w i| = |w i| ^ (1 - q) * |w i| ^ q := h2
        _ ≤ ((2 : ℝ) ^ (-(j : ℝ) - 1)) ^ (1 - q) * |w i| ^ q :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (abs_nonneg _) _)
    · exfalso
      have hp0 : SQMeanEstimation.posPart w i = 0 := by simp [SQMeanEstimation.posPart, h0]
      rw [hp0, abs_zero] at hc
      linarith [hc.1]
  · rw [abs_zero]
    exact mul_nonneg hCpos.le (Real.rpow_nonneg (abs_nonneg _) _)

end Aux_SQMeanEstimation_eq_2

open SQMeanEstimation in
theorem solution {d : ℕ} (q : ℝ) (hq1 : 1 < q) (hq2 : q < 2) (j : ℕ)
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (hμ : ∀ᵐ w ∂μ, lqNorm q w ≤ 1) :
    ∑ i, |(2 : ℝ) ^ j * (∫ w, ringPart j (SQMeanEstimation.posPart w) ∂μ) i| ≤
        (2 : ℝ) ^ j * ((2 : ℝ) ^ (-(j : ℝ) - 1)) ^ (1 - q) ∧
      (2 : ℝ) ^ j * ((2 : ℝ) ^ (-(j : ℝ) - 1)) ^ (1 - q) = (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1)
    := by
  have hC2 : (2 : ℝ) ^ j * ((2 : ℝ) ^ (-(j : ℝ) - 1)) ^ (1 - q)
      = (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_natCast,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  refine ⟨?_, hC2⟩
  have hCpos : 0 < ((2 : ℝ) ^ (-(j : ℝ) - 1)) ^ (1 - q) :=
    Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _) _
  have h2j : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  by_cases hF : Integrable (fun w => ringPart j (SQMeanEstimation.posPart w)) μ
  · have hFi := hF.eval
    have hcoord : ∀ i, (∫ w, ringPart j (SQMeanEstimation.posPart w) ∂μ) i = ∫ w, ringPart j (SQMeanEstimation.posPart w) i ∂μ :=
      fun i => eval_integral hFi i
    have hpt : ∀ᵐ w ∂μ, ∑ i, |ringPart j (SQMeanEstimation.posPart w) i|
        ≤ ((2 : ℝ) ^ (-(j : ℝ) - 1)) ^ (1 - q) := by
      filter_upwards [hμ] with w hw
      have hT : ∑ i, |w i| ^ q ≤ 1 := by
        unfold lqNorm at hw
        by_contra h
        push_neg at h
        have := Real.one_lt_rpow h (by positivity : (0 : ℝ) < 1 / q)
        linarith
      calc ∑ i, |ringPart j (SQMeanEstimation.posPart w) i|
          ≤ ∑ i, ((2 : ℝ) ^ (-(j : ℝ) - 1)) ^ (1 - q) * |w i| ^ q :=
            Finset.sum_le_sum (fun i _ => Aux_SQMeanEstimation_eq_2.coord_bound q hq1 j w i)
        _ = ((2 : ℝ) ^ (-(j : ℝ) - 1)) ^ (1 - q) * ∑ i, |w i| ^ q := by
            rw [Finset.mul_sum]
        _ ≤ ((2 : ℝ) ^ (-(j : ℝ) - 1)) ^ (1 - q) * 1 :=
            mul_le_mul_of_nonneg_left hT hCpos.le
        _ = ((2 : ℝ) ^ (-(j : ℝ) - 1)) ^ (1 - q) := mul_one _
    have hint : Integrable (fun w => ∑ i, |ringPart j (SQMeanEstimation.posPart w) i|) μ :=
      integrable_finsetSum _ (fun i _ => (hFi i).abs)
    have hbound : ∫ w, ∑ i, |ringPart j (SQMeanEstimation.posPart w) i| ∂μ
        ≤ ((2 : ℝ) ^ (-(j : ℝ) - 1)) ^ (1 - q) := by
      have := integral_mono_ae hint (integrable_const _) hpt
      simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using this
    calc ∑ i, |(2 : ℝ) ^ j * (∫ w, ringPart j (SQMeanEstimation.posPart w) ∂μ) i|
        = (2 : ℝ) ^ j * ∑ i, |∫ w, ringPart j (SQMeanEstimation.posPart w) i ∂μ| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [hcoord i, abs_mul, abs_of_pos h2j]
      _ ≤ (2 : ℝ) ^ j * ∑ i, ∫ w, |ringPart j (SQMeanEstimation.posPart w) i| ∂μ := by
          apply mul_le_mul_of_nonneg_left _ h2j.le
          exact Finset.sum_le_sum (fun i _ => abs_integral_le_integral_abs)
      _ = (2 : ℝ) ^ j * ∫ w, ∑ i, |ringPart j (SQMeanEstimation.posPart w) i| ∂μ := by
          rw [integral_finsetSum _ (fun i _ => (hFi i).abs)]
      _ ≤ (2 : ℝ) ^ j * ((2 : ℝ) ^ (-(j : ℝ) - 1)) ^ (1 - q) :=
          mul_le_mul_of_nonneg_left hbound h2j.le
  · rw [integral_undef hF]
    simp only [Pi.zero_apply, mul_zero, abs_zero, Finset.sum_const_zero]
    exact mul_nonneg h2j.le hCpos.le
