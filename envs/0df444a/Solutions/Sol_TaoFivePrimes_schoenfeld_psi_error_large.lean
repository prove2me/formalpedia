-- Prove2me | solution 1 for TaoFivePrimes.schoenfeld_psi_error_large
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T19:17:45.738777+00:00
-- url     : https://prove2.me/submissions/d5a70594-5d4e-4628-885f-16bbfb987436
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_schoenfeld_psi_excess_upper_large
import Theorems.Thm_TaoFivePrimes_schoenfeld_psi_deficit_lower_large
import Mathlib.NumberTheory.Chebyshev

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option linter.all false

open TaoFivePrimes

theorem _root_.solution (y : ℝ) (hy : 10 ^ 8 ≤ y) :
    |Chebyshev.psi y - y| ≤ y / (40 * Real.log y) := by
  exact abs_le.mpr
    ⟨TaoFivePrimes.schoenfeld_psi_deficit_lower_large y hy,
     TaoFivePrimes.schoenfeld_psi_excess_upper_large y hy⟩

#print axioms solution
