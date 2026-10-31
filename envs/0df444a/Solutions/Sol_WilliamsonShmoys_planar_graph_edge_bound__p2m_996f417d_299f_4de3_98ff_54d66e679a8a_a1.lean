-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_edge_bound__p2m_996f417d_299f_4de3_98ff_54d66e679a8a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:38:14.410475+00:00
-- url     : https://prove2.me/submissions/ec4f90de-dfd9-4830-9217-96458d50ee7f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_e3ce4704_f609_45f0_9a05_cff1f4f992c7_a1
import Theorems.Thm_SimpleGraph_edgeSet_ncard_mono__p2m_e3ce4704_f609_45f0_9a05_cff1f4f992c7_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, hH, hEdges⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_e3ce4704_f609_45f0_9a05_cff1f4f992c7_a1
      G hG hV
  have hMono :=
    SimpleGraph.edgeSet_ncard_mono__p2m_e3ce4704_f609_45f0_9a05_cff1f4f992c7_a1
      G H hGH
  omega
