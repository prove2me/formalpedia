-- Prove2me | solution 1 for actuarial_c_inc_dec_level
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:02:41.697225+00:00
-- url     : https://prove2.me/submissions/55438197-35d0-4a4a-a2bf-1467e7497b81

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_inc
import Definitions.Def_actuarial_c_dec

open ActuarialAssurances



theorem solution (n j : ℕ) (hj : j < n) : inc j+dec n j=(n+1 : ℕ) := by
  unfold inc dec; rw [← Nat.cast_add]; congr 1; omega

