-- Prove2me | solution 1 for actuarial_f_member_two_streams_instate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:39:45.066831+00:00
-- url     : https://prove2.me/submissions/4a7ca58a-061c-4bd6-a4c1-9e1f6923afcd

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_awardBase
import Definitions.Def_actuarial_f_memberDue
import Definitions.Def_actuarial_f_memberTrancheOne
import Definitions.Def_actuarial_f_memberTrancheTwo

open ActuarialUnderpinsF

theorem solution (r z i t : ℕ)
    (a b c g0 g1 : ℕ → ℝ) :
    memberTrancheOne r z i t a b g0 + memberTrancheTwo r z i t c g1 =
    (awardBase a b z * g0 t + c z * g1 t) * memberDue r i t := by
  unfold memberTrancheOne memberTrancheTwo
  grind
