-- Prove2me | solution 1 for actuarial_f_af_member_pre1985_not_automatically_covered
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:00:03.208669+00:00
-- url     : https://prove2.me/submissions/276235a3-9df7-4483-baaf-22bc6a23fcea

import Mathlib
import Definitions.Def_actuarial_f_afMemberSection87WeeklyFloor
open ActuarialUnderpinsF

theorem solution
    (cessation gpd t : ℕ)
    (entitled substitute : Bool)
    (relevant current base addition later : ℝ) :
    afMemberSection87WeeklyFloor cessation gpd t
      true false entitled substitute false relevant current base
      addition later 0 = 0 := by
  unfold afMemberSection87WeeklyFloor
  rw [if_neg]
  simp [afMemberSection87Eligible]
