-- Prove2me | solution 1 for PHIP1891.li_terminal
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:56:30.760416+00:00
-- url     : https://prove2.me/submissions/51e65f45-e7ce-4628-9087-e8648c016695

import Mathlib
open MeasureTheory Set

theorem solution (d q c : ℝ) (hc : 0 < c)
    (hidentity : q = -c*d) (hseed : d < 0) (hrh : q ≤ 0) : False := by
  have hp : 0 < -c*d := mul_pos_of_neg_of_neg (neg_neg_of_pos hc) hseed
  linarith
