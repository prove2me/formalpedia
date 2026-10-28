-- Prove2me | solution 1 for actuarial_f_guarantee_pays_after_member_death
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:37:56.937304+00:00
-- url     : https://prove2.me/submissions/228cff75-c3ae-40c0-8778-6787a7e92299

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_estateDue

open ActuarialUnderpinsF

theorem solution (h r g i t : ℕ)
    (he : estateDue h r g i t = 1) : i < t ∧ t < r + g := by
  unfold estateDue at he
  split_ifs at he with H
  · omega
  · norm_num at he
