-- Prove2me | solution 1 for PermanentRollout.affine_sum_range_degree_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/78ab7e4a-c8b5-4947-907d-eee0b8a0be74

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
    (H : ℕ → ℕ) (d N : ℕ) :
    (∑ m ∈ Finset.range N, if d ≤ m then H (m - d) else 0) =
      ∑ m ∈ Finset.range (N - d), H m := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases h : d ≤ N
      · have hs : N + 1 - d = (N - d) + 1 := by omega
        rw [if_pos h, hs, Finset.sum_range_succ]
      · have hN : N - d = 0 := by omega
        have hs : N + 1 - d = 0 := by omega
        simp [h, hN, hs]
end PermanentRollout
