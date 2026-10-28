-- Prove2me | solution 1 for actuarial_f_af_survivor_half_gmp_threshold
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:05:24.603716+00:00
-- url     : https://prove2.me/submissions/c7ddbb16-80a3-4956-8773-52b5630fc05c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_afSurvivorSection87WeeklyFloor

open ActuarialUnderpinsF



theorem solution
    (cessation death gpd t : ℕ)
    (relevant current memberBase appropriate later : ℝ)
    (hhalf : relevant ≤ memberBase / 2) :
    afSurvivorSection87WeeklyFloor cessation death gpd t
      false false true false false relevant current memberBase
      appropriate later 0 = 0 := by
  unfold afSurvivorSection87WeeklyFloor afSurvivorSection87Eligible
  rw [if_neg (fun hh => absurd hh.2.2.2.2.2.2.1 (not_lt.mpr hhalf))]
