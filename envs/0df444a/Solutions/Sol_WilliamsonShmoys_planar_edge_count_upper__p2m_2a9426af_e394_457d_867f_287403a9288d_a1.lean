-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper__p2m_2a9426af_e394_457d_867f_287403a9288d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:42:12.353401+00:00
-- url     : https://prove2.me/submissions/ee154dcf-10f2-4c44-be11-7125e7ab1fe9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_induced_planar_edge_count_upper__p2m_30d6faec_b0bf_4bef_98dc_af9f33dfa7ee_a1
import Theorems.Thm_WilliamsonShmoys_edge_count_from_connected_induced_bounds__p2m_30d6faec_b0bf_4bef_98dc_af9f33dfa7ee_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (hcard : 3 ≤ Fintype.card V) (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  classical
  letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
  apply WilliamsonShmoys.edge_count_from_connected_induced_bounds__p2m_30d6faec_b0bf_4bef_98dc_af9f33dfa7ee_a1 hcard H
  intro s hs hconn
  exact WilliamsonShmoys.connected_induced_planar_edge_count_upper__p2m_30d6faec_b0bf_4bef_98dc_af9f33dfa7ee_a1 H s hdraw hs hconn