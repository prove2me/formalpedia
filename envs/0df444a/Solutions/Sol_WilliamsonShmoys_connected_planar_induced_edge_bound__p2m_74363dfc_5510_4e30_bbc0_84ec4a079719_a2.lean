-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_induced_edge_bound__p2m_74363dfc_5510_4e30_bbc0_84ec4a079719_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:26:32.908234+00:00
-- url     : https://prove2.me/submissions/45272cd1-cc1e-4b3b-ac90-7395e985481a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_planar_face_count_data__p2m_8e79e615_ce68_4197_8611_7fa93173a04e_a2
import Theorems.Thm_WilliamsonShmoys_simple_graph_small_edge_bound__p2m_8e79e615_ce68_4197_8611_7fa93173a04e_a2
import Theorems.Thm_WilliamsonShmoys_euler_face_edge_arithmetic__p2m_8e79e615_ce68_4197_8611_7fa93173a04e_a2

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     K.edgeFinset.card <= max 1 (3 * Fintype.card V - 6)) := by
  classical
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  by_cases hsmall : Fintype.card V < 3
  · have he :=
      WilliamsonShmoys.simple_graph_small_edge_bound__p2m_8e79e615_ce68_4197_8611_7fa93173a04e_a2
        K hsmall
    exact le_trans he (Nat.le_max_left _ _)
  · have hlarge : 3 ≤ Fintype.card V := by omega
    obtain ⟨f, heuler, hfaces⟩ :=
      WilliamsonShmoys.connected_planar_face_count_data__p2m_8e79e615_ce68_4197_8611_7fa93173a04e_a2
        K hK hconn hlarge
    have he :=
      WilliamsonShmoys.euler_face_edge_arithmetic__p2m_8e79e615_ce68_4197_8611_7fa93173a04e_a2
        (Fintype.card V) K.edgeFinset.card f hlarge heuler hfaces
    exact le_trans he (Nat.le_max_right _ _)
