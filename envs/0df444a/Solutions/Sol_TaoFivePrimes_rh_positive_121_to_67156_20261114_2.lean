-- Prove2me | solution 2 for TaoFivePrimes.rh_positive_121_to_67156_20261114
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-21T22:59:38.409954+00:00
-- url     : https://prove2.me/submissions/81dcb170-d275-4786-b302-f90ec0cc5c5f

import Definitions.Def_row23_rh_supp_RH67156SegmentExtended
set_option autoImplicit false
noncomputable section
theorem solution (s : ℂ) (hz : riemannZeta s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 1) (hp : 0 < s.im)
    (ha : (121 : ℝ) ≤ s.im) (hb : s.im ≤ (67156 : ℝ) + 25 / 8192) :
    s.re = 1 / 2:= by
  exact RH67156Count.segment_extended s hz h0 h1 hp ha hb
