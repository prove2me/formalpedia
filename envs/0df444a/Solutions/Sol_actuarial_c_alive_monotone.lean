-- Prove2me | solution 1 for actuarial_c_alive_monotone
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:50:54.320254+00:00
-- url     : https://prove2.me/submissions/38144fb9-97f7-4a86-8661-e50fa7a6d2d7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive

open ActuarialAssurances

theorem solution (k i j : ℕ) (hij : i ≤ j) : alive k j ≤ alive k i := by
  unfold alive
  grind
