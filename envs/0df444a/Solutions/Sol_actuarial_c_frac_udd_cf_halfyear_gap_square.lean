-- Prove2me | solution 1 for actuarial_c_frac_udd_cf_halfyear_gap_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-14T07:02:53.385981+00:00
-- url     : https://prove2.me/submissions/ca553ecd-cf19-4581-b683-06c1bbdb56e5

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_c_frac_uddHalf
import Definitions.Def_actuarial_c_frac_cfHalf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAssurances.Fractional

theorem solution (p : ℝ) (hp : 0 ≤ p) :
    uddHalf p - cfHalf p = (Real.sqrt p - 1)^2 / 2 := by
  unfold uddHalf cfHalf
  have hs : (Real.sqrt p)^2 = p := Real.sq_sqrt hp
  nlinarith
