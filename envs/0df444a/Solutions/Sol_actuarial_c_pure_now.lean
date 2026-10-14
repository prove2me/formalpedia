-- Prove2me | solution 1 for actuarial_c_pure_now
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:58:49.500156+00:00
-- url     : https://prove2.me/submissions/56397610-9c37-4c9b-8c25-6d146994d73f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_total
import Definitions.Def_actuarial_c_purePath
import Definitions.Def_actuarial_c_pure

open ActuarialAssurances

theorem solution (h : ℕ) (v : ℝ) (p : ℕ → ℝ) : pure h 0 v p=total h p := by
  unfold ActuarialAssurances.pure purePath alive total
  refine Finset.sum_congr rfl ?_
  intro k _
  simp [pow_zero]

