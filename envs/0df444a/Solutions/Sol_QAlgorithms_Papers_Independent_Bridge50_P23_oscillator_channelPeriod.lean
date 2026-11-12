-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P23.oscillator_channelPeriod
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T01:50:37.806339+00:00
-- url     : https://prove2.me/submissions/04a21b9b-f997-46ab-9b7e-50c054e3fafe

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P23

noncomputable section

open Filter

open scoped ENNReal NNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Bridge50.P23 in
theorem solution :
    diagonalEvolution (fun n : ℕ => (n : ℝ) + 1 / 2) (2 * Real.pi) = id ∧
    diagonalEvolution (fun n : ℕ => (n : ℝ) + 1 / 2) 0 = id := by
  constructor
  · funext X
    ext i j
    show Complex.exp (-Complex.I * ((2 * Real.pi * (((i : ℕ) : ℝ) + 1 / 2 - (((j : ℕ) : ℝ) + 1 / 2)) : ℝ) : ℂ))
      * X i j = X i j
    have h : (-Complex.I * ((2 * Real.pi * (((i : ℕ) : ℝ) + 1 / 2 - (((j : ℕ) : ℝ) + 1 / 2)) : ℝ) : ℂ))
        = ((-((i : ℤ) - (j : ℤ)) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      ring
    rw [h, Complex.exp_int_mul_two_pi_mul_I, one_mul]
  · funext X
    ext i j
    show Complex.exp (-Complex.I * ((0 * (((i : ℕ) : ℝ) + 1 / 2 - (((j : ℕ) : ℝ) + 1 / 2)) : ℝ) : ℂ))
      * X i j = X i j
    rw [zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]

end
