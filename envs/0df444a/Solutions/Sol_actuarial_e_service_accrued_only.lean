-- Prove2me | solution 1 for actuarial_e_service_accrued_only
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:18:49.785983+00:00
-- url     : https://prove2.me/submissions/b268a9e0-e4fc-4dab-9cbb-50b34698bf24

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_serviceBundle

open ActuarialDeathE

theorem solution (k : ℝ) (salary accrued contributions : ℕ → ℝ) (t : ℕ) : serviceBundle k salary accrued contributions false true false t = accrued t := by
  unfold serviceBundle
  simp
