-- Prove2me | solution 2 for TaoFivePrimes.rosser_schoenfeld_totient_pointwise
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T04:40:47.656008+00:00
-- url     : https://prove2.me/submissions/33b0b96e-d89b-4474-934c-982fb710429a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_small
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_large

theorem _root_.solution (n : ℕ) (hn : 3 ≤ n) :
    (n : ℝ) / Nat.totient n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
        2.50637 / Real.log (Real.log (n : ℝ)) := by
  by_cases h : (n : ℝ) < Real.exp 294
  · exact TaoFivePrimes.rosser_schoenfeld_totient_small n hn h
  · exact TaoFivePrimes.rosser_schoenfeld_totient_large n hn (not_lt.1 h)

#print axioms solution
