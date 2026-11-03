-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_from_euler_face_data__p2m_610b0216_a272_4b4e_8618_1ead071ef542_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:39:59.082047+00:00
-- url     : https://prove2.me/submissions/124b7b16-3d7f-4ff7-a7f5-301c6fd60e58

import Theorems.Thm_WilliamsonShmoys_edge_bound_from_euler_face_data__p2m_610b0216_a272_4b4e_8618_1ead071ef542_a2

import Mathlib

theorem solution
    (n q e : ℕ)
    (D : Type) [Fintype D]
    (face : D → Fin q)
    (hD : Fintype.card D = 2 * e)
    (hEuler : n + q = e + 2)
    (hFaces : ∀ f : Fin q,
      3 ≤ Fintype.card {d : D // face d = f}) :
    e + 6 ≤ 3 * n :=
  WilliamsonShmoys.edge_bound_from_euler_face_data__p2m_610b0216_a272_4b4e_8618_1ead071ef542_a2 n q e D face hD hEuler hFaces