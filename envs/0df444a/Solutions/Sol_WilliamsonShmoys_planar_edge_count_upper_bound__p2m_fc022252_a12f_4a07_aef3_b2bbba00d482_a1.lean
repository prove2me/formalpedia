-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_fc022252_a12f_4a07_aef3_b2bbba00d482_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:09:06.023353+00:00
-- url     : https://prove2.me/submissions/be8acb37-aa4a-4cf7-9820-4b7dd36891d1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_of_connected_induced_bounds__p2m_74363dfc_5510_4e30_bbc0_84ec4a079719_a2
import Theorems.Thm_WilliamsonShmoys_connected_planar_induced_edge_bound__p2m_74363dfc_5510_4e30_bbc0_84ec4a079719_a2
import Theorems.Thm_WilliamsonShmoys_induced_planar_drawing__p2m_74363dfc_5510_4e30_bbc0_84ec4a079719_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     K.edgeFinset.card <= 3 * Fintype.card V - 6) := by
  classical
  apply WilliamsonShmoys.planar_edge_count_of_connected_induced_bounds__p2m_74363dfc_5510_4e30_bbc0_84ec4a079719_a2
    K hcard
  intro s hs
  have hd : HasPlanarDrawingOn (K.induce (↑s : Set V)) :=
    WilliamsonShmoys.induced_planar_drawing__p2m_74363dfc_5510_4e30_bbc0_84ec4a079719_a2
      K hK s
  exact WilliamsonShmoys.connected_planar_induced_edge_bound__p2m_74363dfc_5510_4e30_bbc0_84ec4a079719_a2
    (K.induce (↑s : Set V)) hd hs
