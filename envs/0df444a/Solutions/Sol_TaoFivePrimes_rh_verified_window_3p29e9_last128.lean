-- Prove2me | solution 1 for TaoFivePrimes.rh_verified_window_3p29e9_last128
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T10:41:09.066389+00:00
-- url     : https://prove2.me/submissions/0394153c-ac63-45d3-8460-e9e3f6adb287

import Theorems.Thm_TaoFivePrimes_rh_high_height_window_of_signs_and_count
import Theorems.Thm_TaoFivePrimes_rh_high_height_window_endpoint_signs
import Theorems.Thm_TaoFivePrimes_rh_high_height_window_count_le

theorem solution : ∀ s ∈ RHHighHeight.windowZeros 3289999872 3290000000, s.re=1/2 :=
  TaoFivePrimes.rh_high_height_window_of_signs_and_count
    TaoFivePrimes.rh_high_height_window_endpoint_signs
    TaoFivePrimes.rh_high_height_window_count_le
