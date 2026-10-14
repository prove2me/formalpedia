-- Prove2me | solution 1 for actuarial_c_death_binary
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:34.157321+00:00
-- url     : https://prove2.me/submissions/a823b6cd-691d-4ae2-881d-0af1deb28b90

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death

open ActuarialAssurances

theorem solution (k j : ℕ) : (death k j)^2=death k j := by
  simp [death]
