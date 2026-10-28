-- Prove2me | solution 1 for actuarial_f_phased_pension_at_retirement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:35:19.647145+00:00
-- url     : https://prove2.me/submissions/89758e17-3ebc-4625-9b7d-9c7e459387c1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_deferredIncrease
import Definitions.Def_actuarial_f_phasedPension

open ActuarialUnderpinsF

theorem solution (base : ℝ) (r : ℕ)
    (reval increase : ℕ → ℝ) :
    phasedPension base r r reval increase = base * deferredIncrease r reval := by
  simp [phasedPension, paymentIncrease, compoundGrowth]
