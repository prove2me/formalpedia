-- Prove2me | solution 1 for actuarial_d_first_swap
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:50:50.941969+00:00
-- url     : https://prove2.me/submissions/59efb985-dcc7-4d87-b811-7e67b220d5dd

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

theorem solution (h i j : ℕ) (d : ℕ → ℝ) : firstPath h d i j = firstPath h d j i := by
  simp only [tiePath, ySecondPath, xSecondPath, yFirstPath, xFirstPath, secondPath, firstPath]
  grind
