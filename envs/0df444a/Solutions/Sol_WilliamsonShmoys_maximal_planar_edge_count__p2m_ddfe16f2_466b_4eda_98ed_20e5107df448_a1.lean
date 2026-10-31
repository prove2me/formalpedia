-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_ddfe16f2_466b_4eda_98ed_20e5107df448_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:46:19.702985+00:00
-- url     : https://prove2.me/submissions/d35d8501-34fb-447a-949e-6cb4a870c99b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_embedding_face_counts__p2m_bf52c7e7_38dd_4797_a237_775f0494e419_a2
import Theorems.Thm_WilliamsonShmoys_euler_triangulation_edge_count__p2m_bf52c7e7_38dd_4797_a237_775f0494e419_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn T) (hV : 3 <= Fintype.card V)
    (hMax : forall N : SimpleGraph V, T <= N -> HasPlanarDrawingOn N -> N <= T) :
    3 * Fintype.card V = T.edgeSet.ncard + 6 := by
  let h :=
    WilliamsonShmoys.maximal_planar_embedding_face_counts__p2m_bf52c7e7_38dd_4797_a237_775f0494e419_a2
      T hDraw hV hMax
  let f := Classical.choose h
  have hCounts := Classical.choose_spec h
  exact WilliamsonShmoys.euler_triangulation_edge_count__p2m_bf52c7e7_38dd_4797_a237_775f0494e419_a2
    (Fintype.card V) T.edgeSet.ncard f hCounts.1 hCounts.2