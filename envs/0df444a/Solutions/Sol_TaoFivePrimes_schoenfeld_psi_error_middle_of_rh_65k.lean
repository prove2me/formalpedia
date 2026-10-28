-- Prove2me | solution 1 for TaoFivePrimes.schoenfeld_psi_error_middle_of_rh_65k
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:11:21.534374+00:00
-- url     : https://prove2.me/submissions/841af1b2-5845-4bf8-85be-1ccef77f1a92

import Theorems.Thm_TaoFivePrimes_schoenfeld_psi_error_middle_of_rh_65k_and_sine_weight
import Theorems.Thm_TaoFivePrimes_sine_weight_high_zeros_65000
import Mathlib.Tactic

set_option autoImplicit false
open DusartSmoothing Complex Set

theorem solution
    (hRH : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      0 ≤ s.im → s.im ≤ 65000 → s.re = 1/2)
    (y : ℝ) (hy : Real.exp 23 ≤ y) (hY : y < Real.exp 136) :
    |Chebyshev.psi y - y| ≤ y / (40 * Real.log y) := by
  apply TaoFivePrimes.schoenfeld_psi_error_middle_of_rh_65k_and_sine_weight hRH
  · intro r hr0 hr1 Z hZ hγ
    exact TaoFivePrimes.sine_weight_high_zeros_65000 r hr0 hr1 Z hZ hγ
  · exact hy
  · exact hY
