-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_from_euler_face_count__p2m_5d599c83_54c6_426b_a50f_1d6092e7f607_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:21:05.241634+00:00
-- url     : https://prove2.me/submissions/0e8e13b9-c526-4537-9481-3842199d371e

import Mathlib

theorem solution {V : Type} [Fintype V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hData : ∃ f : Nat, Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * H.edgeSet.ncard) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨f, hEuler, hFaces⟩ := hData
  omega