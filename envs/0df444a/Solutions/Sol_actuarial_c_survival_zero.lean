-- Prove2me | solution 1 for actuarial_c_survival_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:36.181694+00:00
-- url     : https://prove2.me/submissions/120f64a4-9f4b-4894-a99d-0872f9b13c27

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_total
import Definitions.Def_actuarial_c_surv

open ActuarialAssurances

theorem solution (h : ℕ) (p : ℕ → ℝ) : surv h p 0=total h p := by
  simp [surv, alive, total]
