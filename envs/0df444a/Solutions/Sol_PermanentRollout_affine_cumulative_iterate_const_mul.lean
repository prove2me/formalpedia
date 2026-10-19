-- Prove2me | solution 1 for PermanentRollout.affine_cumulative_iterate_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/d74a991d-b30e-4afa-a517-140803d7795a

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
    (d : ℕ) (H : ℕ → ℕ) (j M : ℕ) :
    (affineCumulative^[j]) (fun m => d * H m) M =
      d * (affineCumulative^[j]) H M := by
  induction j generalizing M with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      rw [Function.iterate_succ_apply']
      change
        (∑ i ∈ Finset.range (M + 1),
          (affineCumulative^[j]) (fun m => d * H m) i) =
        d * (∑ i ∈ Finset.range (M + 1),
          (affineCumulative^[j]) H i)
      simp_rw [ih]
      rw [← Finset.mul_sum]
end PermanentRollout
