-- Prove2me | solution 1 for PermanentRollout.affine_cumulative_iterate_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/d11a83b9-aa43-43e5-84cb-1005f4a43733

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_affine_cumulative_mono

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {H K : ℕ → ℕ} (h : ∀ m, H m ≤ K m)
    (j M : ℕ) :
    (affineCumulative^[j]) H M ≤ (affineCumulative^[j]) K M := by
  induction j generalizing M with
  | zero => exact h M
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      rw [Function.iterate_succ_apply']
      exact affine_cumulative_mono (fun m => ih m) M
end PermanentRollout
