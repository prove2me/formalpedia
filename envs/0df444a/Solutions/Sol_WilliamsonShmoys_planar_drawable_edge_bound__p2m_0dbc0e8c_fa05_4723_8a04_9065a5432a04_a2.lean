-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_edge_bound__p2m_0dbc0e8c_fa05_4723_8a04_9065a5432a04_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:01:54.241724+00:00
-- url     : https://prove2.me/submissions/dd7b2e20-f321-42f6-b6b0-409a77dc0235

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation__p2m_9786a817_f7aa_4876_b28c_017cd5fca12a_a1
import Theorems.Thm_WilliamsonShmoys_subgraph_edge_ncard_mono__p2m_9786a817_f7aa_4876_b28c_017cd5fca12a_a1

set_option autoImplicit false

 theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨T, hHT, hTri, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation__p2m_9786a817_f7aa_4876_b28c_017cd5fca12a_a1
      H hV hDraw
  have hMono :=
    WilliamsonShmoys.subgraph_edge_ncard_mono__p2m_9786a817_f7aa_4876_b28c_017cd5fca12a_a1
      H T hHT
  omega