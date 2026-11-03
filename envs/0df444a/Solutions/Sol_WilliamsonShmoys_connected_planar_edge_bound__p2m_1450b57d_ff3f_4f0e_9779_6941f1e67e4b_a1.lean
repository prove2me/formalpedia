-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_1450b57d_ff3f_4f0e_9779_6941f1e67e4b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:13:32.181422+00:00
-- url     : https://prove2.me/submissions/7bc2a66d-3811-4d1e-897f-968d2d05048d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_triangulate_connected_planar_drawing__p2m_182810d1_e6dd_4dca_a527_6379c248c599_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hconnected : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    letI : (G : SimpleGraph V) -> DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    K.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  letI : (G : SimpleGraph V) -> DecidableRel G.Adj := fun G => Classical.decRel G.Adj
  have htri :=
    WilliamsonShmoys.triangulate_connected_planar_drawing__p2m_182810d1_e6dd_4dca_a527_6379c248c599_a1
      K hcard hconnected hdraw
  exact Exists.elim htri fun H hH =>
    calc
      K.edgeFinset.card <= H.edgeFinset.card :=
        Finset.card_le_card (SimpleGraph.edgeFinset_mono hH.1)
      _ = 3 * Fintype.card V - 6 := hH.2