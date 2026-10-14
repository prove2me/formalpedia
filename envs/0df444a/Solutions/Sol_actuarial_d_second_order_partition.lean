-- Prove2me | solution 1 for actuarial_d_second_order_partition
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:50:50.302974+00:00
-- url     : https://prove2.me/submissions/029d4f37-bb9e-493c-b95f-3e222f2b0920

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_firstPath
import Definitions.Def_actuarial_d_secondPath
import Definitions.Def_actuarial_d_xFirstPath
import Definitions.Def_actuarial_d_yFirstPath
import Definitions.Def_actuarial_d_xSecondPath
import Definitions.Def_actuarial_d_ySecondPath
import Definitions.Def_actuarial_d_tiePath

open ActuarialJointD

theorem solution (h i j : ℕ) (d : ℕ → ℝ) : secondPath h d i j = xSecondPath h d i j + ySecondPath h d i j + tiePath h d i j := by
  simp only [tiePath, ySecondPath, xSecondPath, yFirstPath, xFirstPath, secondPath, firstPath]
  grind
