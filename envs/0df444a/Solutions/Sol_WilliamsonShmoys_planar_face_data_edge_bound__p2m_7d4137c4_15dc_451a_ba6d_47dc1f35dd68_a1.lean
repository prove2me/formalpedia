-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_data_edge_bound__p2m_7d4137c4_15dc_451a_ba6d_47dc1f35dd68_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:05:17.632896+00:00
-- url     : https://prove2.me/submissions/76a48961-68eb-4028-b9cc-4e2ed18fb8d2

import Mathlib

theorem solution (n m f : ℕ) (boundary : Fin f → ℕ)
    (hn : 3 ≤ n) (heuler : n + f = m + 2)
    (htotal : (∑ i : Fin f, boundary i) = 2 * m)
    (hface : ∀ i, 3 ≤ boundary i) :
    m ≤ 3 * n - 6 := by
  have hsum : 3 * f ≤ ∑ i : Fin f, boundary i := by
    calc
      3 * f = ∑ i : Fin f, 3 := by simp [Nat.mul_comm]
      _ ≤ ∑ i : Fin f, boundary i := by
        exact Finset.sum_le_sum (fun i _ => hface i)
  omega
