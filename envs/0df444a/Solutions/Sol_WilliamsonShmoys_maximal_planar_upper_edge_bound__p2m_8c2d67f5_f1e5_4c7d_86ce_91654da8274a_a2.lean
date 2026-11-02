-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_upper_edge_bound__p2m_8c2d67f5_f1e5_4c7d_86ce_91654da8274a_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:06:32.362938+00:00
-- url     : https://prove2.me/submissions/9cf54c87-6717-45d1-ac37-2f86b24dd10b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawing_connected_extension__p2m_a60c0160_4029_4185_bfe8_ff4b14f19470_a2
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_a60c0160_4029_4185_bfe8_ff4b14f19470_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hn : 3 <= Fintype.card V) :
    L.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  obtain ⟨H, hsub, hcard, hconn, hdraw⟩ :=
    WilliamsonShmoys.drawing_connected_extension__p2m_a60c0160_4029_4185_bfe8_ff4b14f19470_a2
      L dL hL
  letI : DecidableRel H.Adj := Classical.decRel _
  have hcard' := hcard (Classical.decRel _)
  exact le_trans hcard'
    (WilliamsonShmoys.connected_planar_edge_bound__p2m_a60c0160_4029_4185_bfe8_ff4b14f19470_a2
      H hconn hdraw hn)