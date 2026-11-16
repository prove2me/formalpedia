-- Prove2me | solution 1 for PHIP1891.one_cut_preserves_all_depths
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:10:42.118209+00:00
-- url     : https://prove2.me/submissions/9b3c66e3-60e4-4b31-8f84-af8172d0ac9e

import Mathlib
import Theorems.Thm_PHIP1891_negative_survives
open MeasureTheory Set
open PHIP1891

theorem solution (v w : ℕ → ℝ) (e d : ℝ)
    (hd : 0 < d) (hv : ∀ n, v n ≤ -d)
    (herr : ∀ n, |w n-v n| ≤ e) (he : e < d) :
    ∀ n, w n < 0 := by
  intro n
  exact negative_survives (v n) (w n) e d hd (hv n) (herr n) he
