-- Prove2me | solution 1 for actuarial_d_first_order_partition
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:50:53.878977+00:00
-- url     : https://prove2.me/submissions/5193b942-68a0-411f-8a2e-e8afc66072ea

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

theorem solution (h i j : ℕ) (d : ℕ → ℝ) : firstPath h d i j = xFirstPath h d i j + yFirstPath h d i j + tiePath h d i j := by
  simp only [tiePath, ySecondPath, xSecondPath, yFirstPath, xFirstPath, secondPath, firstPath]
  grind
