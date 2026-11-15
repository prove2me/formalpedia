-- Prove2me | solution 1 for TaoFivePrimes.rh66388_segment_cut_upper_20261115
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-14T20:26:25.630348+00:00
-- url     : https://prove2.me/submissions/f29c9987-c301-45f0-bfce-0a59cbacd11c

import Definitions.Def_row23_rh_supp_RH66388UpperEdge
open Complex
noncomputable section
theorem solution :
    DiffractionCore.argChangeHoriz riemannZeta (66388 : ℝ) 2 (-1) ∈
      Set.Icc RH66388Count.enclosure.L2.val RH66388Count.enclosure.H2.val := by
  exact RH66388Edge.upper_edge
