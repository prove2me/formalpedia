-- Prove2me | solution 1 for actuarial_f_overlap_difference
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:38:23.428608+00:00
-- url     : https://prove2.me/submissions/ce4cdd80-4dd2-431f-a3e3-b5079a274fbb

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_estateDue
import Definitions.Def_actuarial_f_parallelPayment
import Definitions.Def_actuarial_f_replacementPayment
import Definitions.Def_actuarial_f_spouseInstalment

open ActuarialUnderpinsF

theorem solution (h r g z i j t : ℕ)
    (s : ℕ → ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (estateBase ge : ℕ → ℝ) :
    parallelPayment h r g z i j t s gs estateBase ge -
      replacementPayment h r g z i j t s gs estateBase ge =
        if estateDue h r g i t = 1 then
          spouseInstalment h z i j t s gs else 0 := by
  unfold replacementPayment parallelPayment
  split_ifs <;> grind
