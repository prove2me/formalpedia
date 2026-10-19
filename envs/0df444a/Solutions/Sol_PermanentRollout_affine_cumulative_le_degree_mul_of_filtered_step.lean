-- Prove2me | solution 1 for PermanentRollout.affine_cumulative_le_degree_mul_of_filtered_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/7ccbdab9-00d4-47a1-9630-53b14865d816

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_affine_sum_range_degree_shift

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    (Hprev Hnext : ℕ → ℕ) (d : ℕ)
    (hmono : Monotone Hprev)
    (hstep : ∀ m : ℕ,
      Hnext m + (if d ≤ m then Hprev (m - d) else 0) ≤ Hprev m)
    (M : ℕ) :
    affineCumulative Hnext M ≤ d * Hprev M := by
  let N := M + 1
  let a := N - d
  let r := min d N
  have har : a + r = N := by
    dsimp [a, r, N]
    omega
  have hsum :
      (∑ m ∈ Finset.range N, Hnext m) +
        (∑ m ∈ Finset.range a, Hprev m) ≤
          ∑ m ∈ Finset.range N, Hprev m := by
    have h := Finset.sum_le_sum
      (s := Finset.range N) (fun m _ => hstep m)
    simpa [Finset.sum_add_distrib,
      affine_sum_range_degree_shift, a] using h
  have hsplit :
      (∑ m ∈ Finset.range N, Hprev m) =
        (∑ m ∈ Finset.range a, Hprev m) +
          (∑ j ∈ Finset.range r, Hprev (a + j)) := by
    rw [← har, Finset.sum_range_add]
  rw [hsplit] at hsum
  have htail :
      (∑ j ∈ Finset.range r, Hprev (a + j)) ≤ r * Hprev M := by
    calc
      (∑ j ∈ Finset.range r, Hprev (a + j)) ≤
          ∑ _j ∈ Finset.range r, Hprev M := by
        apply Finset.sum_le_sum
        intro j hj
        apply hmono
        have hj' := Finset.mem_range.mp hj
        dsimp [N] at har
        omega
      _ = r * Hprev M := by simp
  have hrd : r ≤ d := min_le_left _ _
  unfold affineCumulative
  change (∑ m ∈ Finset.range N, Hnext m) ≤ d * Hprev M
  have hcancel :
      (∑ m ∈ Finset.range N, Hnext m) ≤
        ∑ j ∈ Finset.range r, Hprev (a + j) := by
    omega
  exact hcancel.trans
    (htail.trans (Nat.mul_le_mul_right _ hrd))
end PermanentRollout
