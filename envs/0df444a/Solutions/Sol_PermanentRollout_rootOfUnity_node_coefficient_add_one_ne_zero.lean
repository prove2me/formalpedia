-- Prove2me | solution 1 for PermanentRollout.rootOfUnity_node_coefficient_add_one_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/ea38825f-dd6d-42e9-9ee1-4eed61800adf

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {d : ℕ} (hd : 0 < d) :
    1 + (-1 : ℂ) ^ (d + 1) * (2 : ℂ) ^ d ≠ 0 := by
  intro h
  have heq : (-1 : ℂ) ^ (d + 1) * (2 : ℂ) ^ d = -1 := by
    linear_combination h
  have hnorm := congrArg norm heq
  norm_num [norm_mul, norm_pow] at hnorm
  have hpow : (1 : ℝ) < 2 ^ d := one_lt_pow₀ (by norm_num) hd.ne'
  linarith
end PermanentRollout
