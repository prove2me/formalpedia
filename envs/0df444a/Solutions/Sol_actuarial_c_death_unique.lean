-- Prove2me | solution 1 for actuarial_c_death_unique
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:50:52.917732+00:00
-- url     : https://prove2.me/submissions/1c78e2c0-c4ab-44ae-b709-004da2b4acf8

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death

open ActuarialAssurances

theorem solution (k i j : ℕ) (hij : i ≠ j) : death k i*death k j=0 := by
  simp only [death]
  grind
