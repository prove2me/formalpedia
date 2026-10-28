-- Prove2me | solution 1 for actuarial_f_no_overlap_after_guarantee
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:38:29.979914+00:00
-- url     : https://prove2.me/submissions/b04c5ebe-cec8-44f5-9e5c-aabd3db788da

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_parallelPayment
import Definitions.Def_actuarial_f_replacementPayment

open ActuarialUnderpinsF

theorem solution (h r g z i j t : ℕ)
    (s : ℕ → ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (estateBase ge : ℕ → ℝ) (ht : r + g ≤ t) :
    parallelPayment h r g z i j t s gs estateBase ge =
      replacementPayment h r g z i j t s gs estateBase ge := by
  have he : estateDue h r g i t = 0 := by
    unfold estateDue; rw [if_neg (by omega)]
  unfold replacementPayment parallelPayment
  rw [he, if_neg (by norm_num)]
