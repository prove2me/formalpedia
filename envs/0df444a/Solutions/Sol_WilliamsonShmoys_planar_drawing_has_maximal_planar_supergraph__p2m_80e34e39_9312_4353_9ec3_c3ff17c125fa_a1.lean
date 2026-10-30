-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_planar_supergraph__p2m_80e34e39_9312_4353_9ec3_c3ff17c125fa_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:51:34.460751+00:00
-- url     : https://prove2.me/submissions/4a7478b7-07d2-4eeb-850b-061413beb178
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_inclusion_maximal_graph__p2m_78ba916f_f700_41ef_a045_eff3bbec17a0_a2

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K → K.edgeSet = H.edgeSet) := by
  exact WilliamsonShmoys.exists_edge_inclusion_maximal_graph__p2m_78ba916f_f700_41ef_a045_eff3bbec17a0_a2
    (P := WilliamsonShmoys.HasPlanarDrawingOn) G hDraw
