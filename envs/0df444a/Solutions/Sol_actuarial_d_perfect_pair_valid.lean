-- Prove2me | solution 1 for actuarial_d_perfect_pair_valid
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T12:59:05.479977+00:00
-- url     : https://prove2.me/submissions/356a543a-2a4c-4dc7-9e95-19185fbf2ba1

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_perfectPairLaw

open ActuarialJointD

theorem solution  : valid 1 perfectPairLaw := by
  refine ⟨?_, ?_⟩
  · intro i _ j _; unfold perfectPairLaw; split_ifs <;> norm_num
  · simp [mass, perfectPairLaw, Finset.sum_range_succ]; norm_num
