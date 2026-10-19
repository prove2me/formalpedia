-- Prove2me | solution 1 for actuarial_d_perfect_pair_joint
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T12:58:17.924198+00:00
-- url     : https://prove2.me/submissions/196f32fb-f8a3-4f94-9072-059900f5f551

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_pxy
import Definitions.Def_actuarial_d_perfectPairLaw

open ActuarialJointD

theorem solution  : pxy 1 perfectPairLaw 1 = (1/2 : ℝ) := by
  simp only [pxy, expect, both, alive, perfectPairLaw, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
