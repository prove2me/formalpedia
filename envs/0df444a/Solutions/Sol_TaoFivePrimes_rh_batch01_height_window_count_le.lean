-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_window_count_le
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T18:19:45.39501+00:00
-- url     : https://prove2.me/submissions/d8890db6-2ef8-448a-b122-338c25b6aad2

import Definitions.Def_TaoFivePrimes_RHHighHeightWindow
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_window_count_from_grid_jets
import Theorems.Thm_TaoFivePrimes_rh_batch01_height_all_contour_jets
theorem solution : (RHHighHeight.windowZeros 3289999744 3289999872).ncard ≤ 409 := by
 exact TaoFivePrimes.rh_batch01_height_window_count_from_grid_jets
  (fun e j k he hj hk=>TaoFivePrimes.rh_batch01_height_all_contour_jets e j k he hj hk)
#print axioms solution
