-- Prove2me | solution 1 for PermanentRollout.affine_cumulative_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/a1a72d5e-43b3-4c63-a48f-9afe610d769e

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
    {H K : ℕ → ℕ} (h : ∀ m, H m ≤ K m) (M : ℕ) :
    affineCumulative H M ≤ affineCumulative K M := by
  unfold affineCumulative
  exact Finset.sum_le_sum (fun i _ => h i)
end PermanentRollout
