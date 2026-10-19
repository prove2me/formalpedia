-- Prove2me | solution 1 for PermanentRollout.freeAffineGateReference_mem_vars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/117dcc57-3214-4362-bf2b-89a4641bcbd7

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
    {k n : ℕ} (r : ℕ) (i : Fin n)
    (hi : Sum.inr i ∈
      (freeAffineGateReference (k := k) (n := n) r).vars) :
    i.val = r := by
  classical
  unfold freeAffineGateReference at hi
  split at hi
  next h =>
    simp only [MvPolynomial.vars_X, Finset.mem_singleton] at hi
    exact congrArg Fin.val (Sum.inr_injective hi)
  next h =>
    simp at hi
end PermanentRollout
