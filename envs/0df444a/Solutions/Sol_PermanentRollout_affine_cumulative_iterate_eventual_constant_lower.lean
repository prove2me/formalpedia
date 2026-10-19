-- Prove2me | solution 1 for PermanentRollout.affine_cumulative_iterate_eventual_constant_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/27983789-f95e-465b-8692-2f39902d5bf1

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
    (H : ℕ → ℕ) (L M₀ : ℕ)
    (heventual : ∀ m, M₀ ≤ m → H m = L)
    (n m : ℕ) :
    L * (m + n).choose n ≤
      (affineCumulative^[n]) H (M₀ + m) := by
  induction n generalizing m with
  | zero =>
      simpa using (heventual (M₀ + m) (by omega)).ge
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change L * (m + (n + 1)).choose (n + 1) ≤
        ∑ i ∈ Finset.range (M₀ + m + 1),
          (affineCumulative^[n]) H i
      have hsplit :
          (∑ i ∈ Finset.range (M₀ + m + 1),
            (affineCumulative^[n]) H i) =
          (∑ i ∈ Finset.range M₀,
            (affineCumulative^[n]) H i) +
          (∑ i ∈ Finset.range (m + 1),
            (affineCumulative^[n]) H (M₀ + i)) := by
        simpa [Nat.add_assoc] using
          (Finset.sum_range_add
            (fun i => (affineCumulative^[n]) H i) M₀ (m + 1))
      calc
        L * (m + (n + 1)).choose (n + 1) =
            ∑ i ∈ Finset.range (m + 1),
              L * (i + n).choose n := by
                rw [← Finset.mul_sum, Nat.sum_range_add_choose]
                congr 1
        _ ≤ ∑ i ∈ Finset.range (m + 1),
              (affineCumulative^[n]) H (M₀ + i) :=
            Finset.sum_le_sum (fun i _ => ih i)
        _ ≤ ∑ i ∈ Finset.range (M₀ + m + 1),
              (affineCumulative^[n]) H i := by
            rw [hsplit]
            omega
end PermanentRollout
