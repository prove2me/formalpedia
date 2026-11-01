-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_graph_exact_edge_count__p2m_022fc3fe_2112_4838_9b2a_056c25ecda08_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:24:21.084378+00:00
-- url     : https://prove2.me/submissions/326a3f7f-1bd1-4c6a-bb2c-c863a0a33da2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_straight_line_triangulation__p2m_9b625ce0_21a3_499d_bb1b_40258fa2706e_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeFinset.card + 6 = 3 * Fintype.card V := by
  obtain ⟨L, dL, p, arc, hp, hseg, hcross, hstraight, hcount⟩ :=
    WilliamsonShmoys.exists_straight_line_triangulation__p2m_9b625ce0_21a3_499d_bb1b_40258fa2706e_a2 hcard
  exact ⟨L, dL, ⟨p, arc, hp, hseg, hcross⟩, hcount⟩