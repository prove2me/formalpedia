-- Prove2me | solution 1 for actuarial_f_indexed_at_base
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:35:05.901974+00:00
-- url     : https://prove2.me/submissions/e3adca3b-16fc-430b-bd2e-11196e37f553

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_indexedPayment

open ActuarialUnderpinsF

theorem solution (base : ℝ) (r : ℕ → ℝ) :
    indexedPayment base r 0 = base := by
  simp [indexedPayment, compoundGrowth]
