-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_2c123b8f_1995_4892_9bf1_663a03a79ac0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:47:33.920217+00:00
-- url     : https://prove2.me/submissions/9ebfdbd9-3128-4d7c-a686-f6b110371ed1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximum_edge_supergraph__p2m_fb475999_bbbb_4d3f_8e03_a58caa743876_a1
import Theorems.Thm_WilliamsonShmoys_maximum_edge_planar_graph_connected__p2m_fb475999_bbbb_4d3f_8e03_a58caa743876_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V, L ≤ T ∧ T.Connected ∧ HasPlanarDrawingOn T := by
  classical
  obtain ⟨Q, dQ, hQ, hLQ, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximum_edge_supergraph__p2m_fb475999_bbbb_4d3f_8e03_a58caa743876_a1
      L (Classical.decRel L.Adj) hL
  have hcard2 : 2 ≤ Fintype.card V := by omega
  have hconn :=
    WilliamsonShmoys.maximum_edge_planar_graph_connected__p2m_fb475999_bbbb_4d3f_8e03_a58caa743876_a1
      Q dQ hcard2 hQ hmax
  exact ⟨Q, hLQ, hconn, hQ⟩