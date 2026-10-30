-- Prove2me | solution 1 for WilliamsonShmoys.euler_face_count_bound__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T20:28:02.279022+00:00
-- url     : https://prove2.me/submissions/69a9ec02-caf0-499b-b7a4-eb63c6c388db

import Definitions.Def_WilliamsonShmoys_PlanarFaceData__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (D : WilliamsonShmoys.PlanarFaceData__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  letI : Fintype D.Faces__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 :=
    D.fintypeFaces__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2
  letI : DecidableEq D.Faces__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 :=
    D.decEqFaces__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2
  have hlen :
      (∑ f : D.Faces__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2, 3) ≤
        ∑ f, D.faceLength__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 f := by
    exact Finset.sum_le_sum (fun f _ =>
      D.lower__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 f)
  have hsum :
      3 * Fintype.card D.Faces__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 ≤
        ∑ f, D.faceLength__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 f := by
    simpa [Nat.mul_comm] using hlen
  have heuler := D.euler__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2
  have hinc := D.incidence__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2
  omega