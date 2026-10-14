-- Prove2me | solution 1 for actuarial_c_pure_no_interest
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:35.787995+00:00
-- url     : https://prove2.me/submissions/3a41404e-5917-4da1-a4d3-45f9f2a6b2e9

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_pureMass

open ActuarialAssurances

theorem solution (h n : ℕ) (p : ℕ → ℝ) : pureMass h n 1 p=surv h p n := by
  simp [pureMass, surv, alive]
