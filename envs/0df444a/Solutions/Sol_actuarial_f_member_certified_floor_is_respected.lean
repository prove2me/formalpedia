-- Prove2me | solution 1 for actuarial_f_member_certified_floor_is_respected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:56:52.989451+00:00
-- url     : https://prove2.me/submissions/65c4e3af-4f63-45fe-a7ac-a415ebfe2f0e

import Mathlib
import Definitions.Def_actuarial_f_gmpCertifiedMemberPayable
open ActuarialUnderpinsF

theorem solution
    (contractual certifiedStatutoryFloor : ℝ) :
    certifiedStatutoryFloor ≤
      gmpCertifiedMemberPayable contractual certifiedStatutoryFloor := by
  exact le_max_right _ _
