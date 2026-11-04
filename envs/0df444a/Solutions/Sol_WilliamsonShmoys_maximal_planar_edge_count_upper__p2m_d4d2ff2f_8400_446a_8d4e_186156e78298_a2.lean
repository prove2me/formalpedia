-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_d4d2ff2f_8400_446a_8d4e_186156e78298_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:05:47.333473+00:00
-- url     : https://prove2.me/submissions/abfffc00-1174-4878-aadb-8f3d53ad392a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph__p2m_e8818a47_c6bb_451e_9488_1f3faaa47e8f_a3
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_upper__p2m_e8818a47_c6bb_451e_9488_1f3faaa47e8f_a3
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      K.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  classical
  obtain ⟨H, hH, hconn, hmono⟩ :=
    WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_e8818a47_c6bb_451e_9488_1f3faaa47e8f_a3
      K hK hcard
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  exact Nat.le_trans hmono
    (WilliamsonShmoys.connected_planar_edge_count_upper__p2m_e8818a47_c6bb_451e_9488_1f3faaa47e8f_a3
      H hH hconn hcard)