-- Prove2me | solution 1 for actuarial_d_reversion_prob
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T13:04:58.606772+00:00
-- url     : https://prove2.me/submissions/70011ce8-9a42-4e8b-b3e0-d01c98c76e73

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_px
import Definitions.Def_actuarial_d_py
import Definitions.Def_actuarial_d_pxy
import Definitions.Def_actuarial_d_prev
import Definitions.Def_actuarial_d_plast
import Definitions.Def_actuarial_d_pureLast
import Definitions.Def_actuarial_d_pureX
import Definitions.Def_actuarial_d_pureY
import Definitions.Def_actuarial_d_pureJoint

open ActuarialJointD

theorem solution (h t : ℕ) (p : ℕ → ℕ → ℝ) : prev h p t = py h p t - pxy h p t := by
  simp only [prev, py, pxy, expect, onlyY, both, dead]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

