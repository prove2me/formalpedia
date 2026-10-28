-- Prove2me | solution 1 for actuarial_f_cii_spouse_bounded
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:59:58.048107+00:00
-- url     : https://prove2.me/submissions/60f7b5b2-8c19-4bb0-9b2e-f46ebf2177c0

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseDue
import Definitions.Def_actuarial_d_onlyY

open ActuarialUnderpinsF



theorem solution (h i j t : ℕ) (ht : t ≤ h) :
    ActuarialUnderpinsF.spouseDue h i j t = ActuarialJointD.onlyY i j t := by
  unfold spouseDue
  split_ifs with hi
  · rfl
  · simp [ActuarialJointD.onlyY, ActuarialJointD.dead, ActuarialJointD.alive,
      show t ≤ i by omega]
