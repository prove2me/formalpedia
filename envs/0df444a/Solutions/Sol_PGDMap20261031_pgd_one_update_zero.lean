-- Prove2me | solution 1 for PGDMap20261031.pgd_one_update_zero
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T13:05:52.493081+00:00
-- url     : https://prove2.me/submissions/9ecc5a24-cf18-41fd-aefa-a67ce58b1041

import Mathlib.Tactic
import Definitions.Def_PGDMap20261031_Stepsize
open PGDMap20261031

theorem solution : IsStrictCurveMin 1 0 1 := by
  unfold IsStrictCurveMin
  refine ⟨by norm_num [validStep], ?_⟩
  intro u hu hne
  have hden : 0 < u * (2 - u) := mul_pos hu.1 (sub_pos.mpr hu.2)
  have hsq : 0 < (u - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  norm_num [curve, curveOne]
  exact (lt_div_iff₀ hden).mpr (by nlinarith)
