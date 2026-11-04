-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_6400a378_148c_4107_bf45_1bb685620500_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:30:36.30789+00:00
-- url     : https://prove2.me/submissions/54a90764-eed4-404e-8090-647b778a10c6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_upper_bound__p2m_ee19bce3_aed2_4043_9cb4_9bf993438165_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_induce__p2m_ee19bce3_aed2_4043_9cb4_9bf993438165_a1
import Theorems.Thm_WilliamsonShmoys_edge_bound_of_connected_induced_subgraphs__p2m_ee19bce3_aed2_4043_9cb4_9bf993438165_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hT : HasPlanarDrawingOn T) :
    (letI : DecidableRel T.Adj := Classical.decRel T.Adj
     T.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  exact WilliamsonShmoys.edge_bound_of_connected_induced_subgraphs__p2m_ee19bce3_aed2_4043_9cb4_9bf993438165_a1
    T hV (fun s hs hconn => by
      have hcard : 3 ≤ Fintype.card (↑(s : Set V)) := by simpa using hs
      have hdrawing : HasPlanarDrawingOn (T.induce (↑(s : Set V))) :=
        WilliamsonShmoys.planar_drawingOn_induce__p2m_ee19bce3_aed2_4043_9cb4_9bf993438165_a1 T hT s
      exact WilliamsonShmoys.connected_planar_edge_upper_bound__p2m_ee19bce3_aed2_4043_9cb4_9bf993438165_a1
        (T.induce (↑(s : Set V))) hcard hdrawing hconn)