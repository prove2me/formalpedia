-- Prove2me | solution 1 for PermanentRollout.affine_cumulative_iterate_le_degree_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/9761bdd6-b232-47c8-9616-6b11fb64f632

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_affine_cumulative_le_degree_mul_of_filtered_step
import Theorems.Thm_PermanentRollout_affine_cumulative_iterate_mono
import Theorems.Thm_PermanentRollout_affine_cumulative_iterate_const_mul

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    (H : ℕ → ℕ → ℕ) (d : ℕ → ℕ) (n : ℕ)
    (hmono : ∀ i, i < n → Monotone (H i))
    (hstep : ∀ i, i < n → ∀ m,
      H (i + 1) m +
        (if d i ≤ m then H i (m - d i) else 0) ≤ H i m)
    (M : ℕ) :
    (affineCumulative^[n]) (H n) M ≤
      (∏ i ∈ Finset.range n, d i) * H 0 M := by
  have aux : ∀ j, j ≤ n → ∀ m,
      (affineCumulative^[j]) (H j) m ≤
        (∏ i ∈ Finset.range j, d i) * H 0 m := by
    intro j hj
    induction j with
    | zero =>
        intro m
        simp
    | succ j ih =>
        have hjn : j < n := by omega
        intro m
        have hone : ∀ q,
            affineCumulative (H (j + 1)) q ≤ d j * H j q :=
          affine_cumulative_le_degree_mul_of_filtered_step
            (H j) (H (j + 1)) (d j)
            (hmono j hjn) (hstep j hjn)
        calc
          (affineCumulative^[j + 1]) (H (j + 1)) m =
              (affineCumulative^[j])
                (affineCumulative (H (j + 1))) m := by
                  rw [Function.iterate_succ_apply]
          _ ≤ (affineCumulative^[j])
                (fun q => d j * H j q) m :=
              affine_cumulative_iterate_mono hone j m
          _ = d j * (affineCumulative^[j]) (H j) m :=
              affine_cumulative_iterate_const_mul (d j) (H j) j m
          _ ≤ d j * ((∏ i ∈ Finset.range j, d i) * H 0 m) :=
              Nat.mul_le_mul_left (d j) (ih (by omega) m)
          _ = (∏ i ∈ Finset.range (j + 1), d i) * H 0 m := by
              rw [Finset.prod_range_succ]
              ac_rfl
  exact aux n le_rfl M
end PermanentRollout
