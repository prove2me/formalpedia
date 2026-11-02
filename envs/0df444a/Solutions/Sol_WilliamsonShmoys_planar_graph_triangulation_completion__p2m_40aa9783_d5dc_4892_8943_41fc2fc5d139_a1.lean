-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_triangulation_completion__p2m_40aa9783_d5dc_4892_8943_41fc2fc5d139_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:06:24.504032+00:00
-- url     : https://prove2.me/submissions/bc90a2ba-04d8-42bf-ac48-51b91f9257fa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_supergraph__p2m_f3f7a3a7_d237_45a5_b1fd_f31e0f1c8fc4_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_f3f7a3a7_d237_45a5_b1fd_f31e0f1c8fc4_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn K) :
    ∃ J : SimpleGraph V, K.edgeSet ⊆ J.edgeSet ∧
      HasPlanarDrawingOn J ∧
      J.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨J, hKJ, hJplanar, hJmax⟩ :=
    WilliamsonShmoys.drawable_graph_has_maximal_supergraph__p2m_f3f7a3a7_d237_45a5_b1fd_f31e0f1c8fc4_a1
      K hcard hplanar
  have hcount :=
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_f3f7a3a7_d237_45a5_b1fd_f31e0f1c8fc4_a1
      J hcard hJplanar hJmax
  exact ⟨J, hKJ, hJplanar, hcount⟩