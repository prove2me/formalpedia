-- Prove2me | solution 1 for SpenglerVertical.DoubleMarginalization.figure1_example
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:47:47.610001+00:00
-- url     : https://prove2.me/submissions/a8152579-4b74-498a-ae90-5d1c5202f59d

import Definitions.Def_SpenglerVertical_DoubleMarginalization_Model

set_option autoImplicit false
open SpenglerVertical.DoubleMarginalization
theorem solution :
    IsProfitMax (linearDemand 40 4) 20 30 ∧ linearDemand 40 4 30 = 40 ∧
    IsProfitMax (linearDemand 90 2) (30 + 20) 70 ∧ linearDemand 90 2 70 = 40 ∧
    IsProfitMax (linearDemand 140 (8 / 5)) (70 + 20) 115 ∧
    IsProfitMax (linearDemand 140 (8 / 5)) (20 + 20 + 20) 100 ∧
    linearDemand 140 (8 / 5) 115 = 40 ∧
    linearDemand 140 (8 / 5) 100 = 64 ∧
    linearDemand 140 (8 / 5) 60 = 128 ∧
    (115 - (70 + 20)) * linearDemand 140 (8 / 5) 115 = 1000 ∧
    (20 + 20 + 20) * linearDemand 140 (8 / 5) 115 = 2400 ∧
    (30 - 20) * linearDemand 140 (8 / 5) 115 + (70 - (20 + 30)) * linearDemand 140 (8 / 5) 115
      + (115 - (20 + 70)) * linearDemand 140 (8 / 5) 115 = 2200 ∧
    115 * linearDemand 140 (8 / 5) 115 = 4600 ∧
    (100 - (20 + 20 + 20)) * linearDemand 140 (8 / 5) 100 = 2560 ∧
    (20 + 20 + 20) * linearDemand 140 (8 / 5) 100 = 3840 ∧
    (∫ x in (100 : ℝ)..115, linearDemand 140 (8 / 5) x) = 780 ∧
    linearDemand 140 (8 / 5) 115 * (115 - 100)
      + (linearDemand 140 (8 / 5) 100 - linearDemand 140 (8 / 5) 115) * (115 - 100) * (1 / 2)
      = 780 := by
  have hmax1 : IsProfitMax (linearDemand 40 4) 20 30 := by
    intro x
    unfold profit linearDemand
    nlinarith [sq_nonneg (x - 30)]
  have hmax2 : IsProfitMax (linearDemand 90 2) (30 + 20) 70 := by
    intro x
    unfold profit linearDemand
    nlinarith [sq_nonneg (x - 70)]
  have hmax3 : IsProfitMax (linearDemand 140 (8 / 5)) (70 + 20) 115 := by
    intro x
    unfold profit linearDemand
    nlinarith [sq_nonneg (x - 115)]
  have hmax4 : IsProfitMax (linearDemand 140 (8 / 5)) (20 + 20 + 20) 100 := by
    intro x
    unfold profit linearDemand
    nlinarith [sq_nonneg (x - 100)]
  have hint : (∫ x in (100 : ℝ)..115, linearDemand 140 (8 / 5) x) = 780 := by
    unfold linearDemand
    rw [intervalIntegral.integral_const_mul]
    have hi : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 100 115 :=
      continuous_id.intervalIntegrable 100 115
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi]
    norm_num
  norm_num at hmax2 hmax3 hmax4
  rw [hint]
  norm_num [hmax1, hmax2, hmax3, hmax4, linearDemand]

