-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_face_count_data__p2m_8e79e615_ce68_4197_8611_7fa93173a04e_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:57:24.649823+00:00
-- url     : https://prove2.me/submissions/a1351a0f-80a3-494a-a4d1-9fa104da1c3b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_euler_face_count__p2m_471d7036_f9f4_4c2e_9af1_ae12e523e288_a2
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_471d7036_f9f4_4c2e_9af1_ae12e523e288_a3
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     ∃ f : ℕ,
       Fintype.card V + f = K.edgeFinset.card + 2 ∧
       3 * f ≤ 2 * K.edgeFinset.card) := by
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  obtain ⟨f, heuler⟩ :=
    WilliamsonShmoys.connected_planar_euler_face_count__p2m_471d7036_f9f4_4c2e_9af1_ae12e523e288_a2
      K hK hconn
  have hedge :=
    WilliamsonShmoys.planar_edge_bound__p2m_471d7036_f9f4_4c2e_9af1_ae12e523e288_a3
      K hK hconn hcard
  refine ⟨f, heuler, ?_⟩
  omega