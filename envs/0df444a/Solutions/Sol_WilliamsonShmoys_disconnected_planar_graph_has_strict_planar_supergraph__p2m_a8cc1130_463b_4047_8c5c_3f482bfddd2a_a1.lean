-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_planar_graph_has_strict_planar_supergraph__p2m_a8cc1130_463b_4047_8c5c_3f482bfddd2a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:55:13.186576+00:00
-- url     : https://prove2.me/submissions/a82c92fa-4354-464b-b5b9-c50dc41a6bca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_addable_bridge_gives_strict_planar_supergraph__p2m_6953b2d1_377a_4f12_a204_4d1226429a63_a1
import Theorems.Thm_WilliamsonShmoys_disconnected_drawing_has_addable_bridge__p2m_6953b2d1_377a_4f12_a204_4d1226429a63_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hNotConnected : ¬ H.Connected) :
    ∃ M : SimpleGraph V,
      H ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M ≠ H := by
  obtain ⟨p, arc, hp, hEdges, hCross, u, v, c, huv, hnotadj,
      hccont, hcinj, hc0, hc1, hcvertices, hccross⟩ :=
    WilliamsonShmoys.disconnected_drawing_has_addable_bridge__p2m_6953b2d1_377a_4f12_a204_4d1226429a63_a1
      H hH hV hNotConnected
  exact WilliamsonShmoys.addable_bridge_gives_strict_planar_supergraph__p2m_6953b2d1_377a_4f12_a204_4d1226429a63_a1
    H p arc hp hEdges hCross u v c huv hnotadj hccont hcinj hc0 hc1 hcvertices hccross