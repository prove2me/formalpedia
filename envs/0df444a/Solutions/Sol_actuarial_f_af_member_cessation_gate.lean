-- Prove2me | solution 1 for actuarial_f_af_member_cessation_gate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:05:06.962033+00:00
-- url     : https://prove2.me/submissions/0400b55f-385c-4494-b9ea-fa51bba56a29

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_afMemberSection87WeeklyFloor

open ActuarialUnderpinsF



theorem solution
    (cessation gpd t : ℕ)
    (retired entitled substitute : Bool)
    (relevant current base addition later : ℝ)
    (h : gpd ≤ cessation) :
    afMemberSection87WeeklyFloor cessation gpd t
      retired false entitled substitute false relevant current base
      addition later 0 = 0 := by
  unfold afMemberSection87WeeklyFloor afMemberSection87Eligible
  rw [if_neg (fun hh => absurd hh.1 (by omega))]
