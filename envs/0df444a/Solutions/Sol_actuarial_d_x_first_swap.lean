-- Prove2me | solution 1 for actuarial_d_x_first_swap
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:39.884003+00:00
-- url     : https://prove2.me/submissions/c7a038ad-45e1-4f11-8e33-c80443588ad8

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

theorem solution (h i j : ℕ) (d : ℕ → ℝ) : xFirstPath h d i j = yFirstPath h d j i := by
  simp [tiePath, ySecondPath, xSecondPath, yFirstPath, xFirstPath, secondPath, firstPath]
