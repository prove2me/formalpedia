-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_from_euler_certificate_repair4_917de119
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:07:17.820982+00:00
-- url     : https://prove2.me/submissions/98d6b548-3132-48ae-920d-2fef284c22c6

import Mathlib

set_option autoImplicit false

theorem solution
    {V F : Type} [Fintype V] [Fintype F]
    (G : SimpleGraph V)
    (boundaryLength : F → ℕ)
    (hFace : ∀ f : F, 3 ≤ boundaryLength f)
    (hIncidence : Finset.sum Finset.univ boundaryLength = 2 * G.edgeSet.ncard)
    (hEuler : Fintype.card V + Fintype.card F = G.edgeSet.ncard + 2) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  have hFaces :
      Finset.sum Finset.univ (fun _ : F => 3) ≤
        Finset.sum Finset.univ boundaryLength := by
    exact Finset.sum_le_sum (fun f _ => hFace f)
  have hConst :
      Finset.sum Finset.univ (fun _ : F => 3) = 3 * Fintype.card F := by
    simp [Nat.mul_comm]
  rw [hConst, hIncidence] at hFaces
  omega