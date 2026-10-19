-- Prove2me | solution 1 for actuarial_d_product_pair_joint
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T12:59:56.891152+00:00
-- url     : https://prove2.me/submissions/b6aeb482-2643-47ed-bb84-70d46aa02faf

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_pxy
import Definitions.Def_actuarial_d_productPairLaw

open ActuarialJointD

theorem solution  : pxy 1 productPairLaw 1 = (1/4 : ℝ) := by
  simp only [pxy, expect, both, alive, productPairLaw, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
