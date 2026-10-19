-- Prove2me | solution 1 for PermanentRollout.rootOfUnity_node_coefficient_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/f2eff546-ae92-4df4-aef3-89c29eda02da

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution (d : ℕ) :
    ((-1 : ℂ) ^ (d + 1) * (2 : ℂ) ^ d) ≠ 0 := by
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))
end PermanentRollout
