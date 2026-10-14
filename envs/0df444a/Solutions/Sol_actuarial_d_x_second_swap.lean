-- Prove2me | solution 1 for actuarial_d_x_second_swap
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:39.930994+00:00
-- url     : https://prove2.me/submissions/63463326-d663-4506-9460-d13e14bf6f03

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

theorem solution (h i j : ℕ) (d : ℕ → ℝ) : xSecondPath h d i j = ySecondPath h d j i := by
  simp [tiePath, ySecondPath, xSecondPath, yFirstPath, xFirstPath, secondPath, firstPath]
