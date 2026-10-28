-- Prove2me | solution 1 for WilliamsonShmoys.euler_face_counting_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:18:26.768016+00:00
-- url     : https://prove2.me/submissions/425c2852-eb13-40c9-8105-6ceef4ec82b0

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (hcert : ∃ (m : ℕ) (boundaryLength : Fin m → ℕ),
      Fintype.card V + m = K.edgeSet.ncard + 2 ∧
      (∑ f : Fin m, boundaryLength f) = 2 * K.edgeSet.ncard ∧
      ∀ f, 3 ≤ boundaryLength f) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  rcases hcert with ⟨m, boundaryLength, hEuler, hTotal, hBound⟩
  have hsumLower : (∑ f : Fin m, 3) ≤ ∑ f : Fin m, boundaryLength f := by
    apply Finset.sum_le_sum
    intro f hf
    exact hBound f
  have hmul : 3 * m ≤ ∑ f : Fin m, boundaryLength f := by
    simpa [Nat.mul_comm] using hsumLower
  omega