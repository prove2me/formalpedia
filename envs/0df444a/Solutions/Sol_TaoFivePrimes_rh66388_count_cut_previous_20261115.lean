-- Prove2me | solution 1 for TaoFivePrimes.rh66388_count_cut_previous_20261115
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-14T19:54:14.894994+00:00
-- url     : https://prove2.me/submissions/bb2c78f2-cdd6-4474-a33c-384ee08030e7

import Definitions.Def_row23_rh_supp_RH66132LineZeroLowerBound
theorem solution : RS5.BandZeros (121 : ℝ) (66132 : ℝ) 86917 := by
  exact RH66132NewBand.line_zero_lower_bound_121_66132
