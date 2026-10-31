-- Prove2me | solution 1 for WilliamsonShmoys.face_data_edge_bound__p2m_93e8e51b_b659_4e57_adae_24ec3eefdfaa_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:47:46.127985+00:00
-- url     : https://prove2.me/submissions/42d8bb38-9c4e-4040-87c2-2ab936de8d4b

import Mathlib

set_option autoImplicit false

theorem solution
    (n m k : ℕ) (boundary : Fin k → ℕ)
    (hEuler : n + k = m + 2)
    (hBoundarySum : (∑ i, boundary i) = 2 * m)
    (hFaceLength : ∀ i, 3 ≤ boundary i) :
    m + 6 ≤ 3 * n := by
  have hsum : (∑ i : Fin k, (3 : ℕ)) ≤ ∑ i : Fin k, boundary i := by
    apply Finset.sum_le_sum
    intro i hi
    exact hFaceLength i
  have hkm : 3 * k ≤ 2 * m := by
    simpa [Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
      Nat.mul_comm] using hsum.trans_eq hBoundarySum
  omega