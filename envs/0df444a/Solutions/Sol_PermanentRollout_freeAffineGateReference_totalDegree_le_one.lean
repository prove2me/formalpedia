-- Prove2me | solution 1 for PermanentRollout.freeAffineGateReference_totalDegree_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/50c52bf7-4985-4a8f-b363-6b04cd73dedc

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {k n : ℕ} (r : ℕ) :
    (freeAffineGateReference (k := k) (n := n) r).totalDegree ≤ 1 := by
  classical
  unfold freeAffineGateReference
  split <;> simp
end PermanentRollout
