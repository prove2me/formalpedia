-- Prove2me | solution 1 for TaoFivePrimes.theorem51_sharp_transfer_gap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T14:14:24.704864+00:00
-- url     : https://prove2.me/submissions/a696fd78-2b88-409c-bbee-b77a891bf548
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_theorem51_sharp_transfer_gap_global_cancellation

open scoped BigOperators

theorem solution
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    (∑ d ∈ TaoFivePrimes.theorem51Divisors U V,
        (‖(if d ≤ ⌊U⌋₊ then (ArithmeticFunction.moebius d : ℂ) else 0)‖ *
            ‖TaoFivePrimes.typeISlabS1 x alpha d‖
          + ‖(((TaoFivePrimes.vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ))‖ *
              ‖TaoFivePrimes.typeISlabS0 x alpha d‖))
      + ‖TaoFivePrimes.typeISlabS3 x alpha U V‖
    ≤ ∑ d ∈ TaoFivePrimes.theorem51Divisors U V,
        (‖TaoFivePrimes.typeISlabS1 x alpha d‖ +
          Real.log d * ‖TaoFivePrimes.typeISlabS0 x alpha d‖) := by
  have hCancel :=
    TaoFivePrimes.theorem51_sharp_transfer_gap_global_cancellation
      x alpha U V hU hV hUx hVx hUVx hUV2
  have hIdentity :
      (∑ d ∈ TaoFivePrimes.theorem51Divisors U V,
          (‖(if d ≤ ⌊U⌋₊ then (ArithmeticFunction.moebius d : ℂ) else 0)‖ *
              ‖TaoFivePrimes.typeISlabS1 x alpha d‖
            + ‖(((TaoFivePrimes.vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ))‖ *
                ‖TaoFivePrimes.typeISlabS0 x alpha d‖))
        + (∑ d ∈ TaoFivePrimes.theorem51Divisors U V,
          ((1 - ‖(if d ≤ ⌊U⌋₊ then (ArithmeticFunction.moebius d : ℂ) else 0)‖) *
              ‖TaoFivePrimes.typeISlabS1 x alpha d‖
            + (Real.log d -
                ‖(((TaoFivePrimes.vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ))‖) *
                ‖TaoFivePrimes.typeISlabS0 x alpha d‖))
        = ∑ d ∈ TaoFivePrimes.theorem51Divisors U V,
          (‖TaoFivePrimes.typeISlabS1 x alpha d‖ +
            Real.log d * ‖TaoFivePrimes.typeISlabS0 x alpha d‖) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  calc
    (∑ d ∈ TaoFivePrimes.theorem51Divisors U V,
        (‖(if d ≤ ⌊U⌋₊ then (ArithmeticFunction.moebius d : ℂ) else 0)‖ *
            ‖TaoFivePrimes.typeISlabS1 x alpha d‖
          + ‖(((TaoFivePrimes.vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ))‖ *
              ‖TaoFivePrimes.typeISlabS0 x alpha d‖))
        + ‖TaoFivePrimes.typeISlabS3 x alpha U V‖
      ≤ (∑ d ∈ TaoFivePrimes.theorem51Divisors U V,
          (‖(if d ≤ ⌊U⌋₊ then (ArithmeticFunction.moebius d : ℂ) else 0)‖ *
              ‖TaoFivePrimes.typeISlabS1 x alpha d‖
            + ‖(((TaoFivePrimes.vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ))‖ *
                ‖TaoFivePrimes.typeISlabS0 x alpha d‖))
          + (∑ d ∈ TaoFivePrimes.theorem51Divisors U V,
          ((1 - ‖(if d ≤ ⌊U⌋₊ then (ArithmeticFunction.moebius d : ℂ) else 0)‖) *
              ‖TaoFivePrimes.typeISlabS1 x alpha d‖
            + (Real.log d -
                ‖(((TaoFivePrimes.vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ))‖) *
                ‖TaoFivePrimes.typeISlabS0 x alpha d‖)) := by
      exact add_le_add_right hCancel _
    _ = ∑ d ∈ TaoFivePrimes.theorem51Divisors U V,
          (‖TaoFivePrimes.typeISlabS1 x alpha d‖ +
            Real.log d * ‖TaoFivePrimes.typeISlabS0 x alpha d‖) := hIdentity
