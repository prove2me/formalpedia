-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_window_count_le
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T15:02:24.457993+00:00
-- url     : https://prove2.me/submissions/27830698-3033-4858-9fdd-3c366dfa303f

import Definitions.Def_TaoFivePrimes_RHHighHeightWindow
import Theorems.Thm_TaoFivePrimes_rh_high_height_window_count_from_grid_jets
import Theorems.Thm_TaoFivePrimes_rh_high_height_all_contour_jets
theorem solution : (RHHighHeight.windowZeros 3289999872 3290000000).ncard ≤ 409 := by
 exact TaoFivePrimes.rh_high_height_window_count_from_grid_jets
  (fun e j k he hj hk=>TaoFivePrimes.rh_high_height_all_contour_jets e j k he hj hk)
#print axioms solution
