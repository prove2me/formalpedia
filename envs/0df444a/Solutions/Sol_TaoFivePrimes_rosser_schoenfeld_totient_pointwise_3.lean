-- Prove2me | solution 3 for TaoFivePrimes.rosser_schoenfeld_totient_pointwise
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:40:45.795848+00:00
-- url     : https://prove2.me/submissions/efd67078-c0a9-47fd-bc52-62cfa340f5b3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_small
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_large

theorem solution (n : ℕ) (hn : 3 ≤ n) :
    (n : ℝ) / Nat.totient n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
        2.50637 / Real.log (Real.log (n : ℝ)) := by
  by_cases hfin : (n : ℝ) < Real.exp 294
  · exact TaoFivePrimes.rosser_schoenfeld_totient_small n hn hfin
  · exact TaoFivePrimes.rosser_schoenfeld_totient_large n hn (not_lt.mp hfin)
