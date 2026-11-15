-- Prove2me | solution 1 for TaoFivePrimes.rh66388_count_cut_band_20261115
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-14T19:51:51.082831+00:00
-- url     : https://prove2.me/submissions/021162ef-2560-4e81-b7ff-2eba3013519c

import Definitions.Def_row23_rh_supp_RH66388BandZeros
theorem solution : RS5.BandZeros (66132 : ℝ) (66388 : ℝ) 378 := by
  exact RH66388NewBand.line_zeros
