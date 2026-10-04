-- Prove2me | solution 1 for WheelerDeWitt.volumeDensity_pos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T00:21:22.13762+00:00
-- url     : https://prove2.me/submissions/d5dfdabc-5015-4128-ae9f-09061af61418

import Mathlib
import Definitions.Def_wdw_canonical_operators
set_option autoImplicit false

open WheelerDeWitt in
theorem solution {C X : Type*} (g : Geometry C X) (q : C) (x : X) :
    0 < volumeDensity g q x := by
  unfold volumeDensity
  exact Real.sqrt_pos.mpr (g.determinant_pos q x)
