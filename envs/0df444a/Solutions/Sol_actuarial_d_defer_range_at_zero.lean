-- Prove2me | solution 1 for actuarial_d_defer_range_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:37.51564+00:00
-- url     : https://prove2.me/submissions/e16eebfe-e132-4e53-9a79-397696e171af

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_annRange
import Definitions.Def_actuarial_d_annPath

open ActuarialJointD

theorem solution (n : ℕ) (d b s : ℕ → ℝ) : annRange 0 n d b s = annPath n d b s := by
  simp [annPath, annRange]
