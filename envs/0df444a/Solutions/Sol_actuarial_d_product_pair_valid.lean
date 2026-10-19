-- Prove2me | solution 1 for actuarial_d_product_pair_valid
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T13:01:49.96326+00:00
-- url     : https://prove2.me/submissions/94a5be25-65e8-4ae6-b138-222faa7b05ef

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_productPairLaw

open ActuarialJointD

theorem solution  : valid 1 productPairLaw := by
  refine ⟨?_, ?_⟩
  · intro i _ j _; unfold productPairLaw; split_ifs <;> norm_num
  · simp [mass, productPairLaw, Finset.sum_range_succ]; norm_num
