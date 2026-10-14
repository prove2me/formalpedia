-- Prove2me | solution 1 for actuarial_c_geometric_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:35.470306+00:00
-- url     : https://prove2.me/submissions/73d46402-8637-4485-b81f-1af8cbcd5052

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_geom

open ActuarialAssurances

theorem solution (j : ℕ) : geom 1 j=1 := by
  simp [geom]
