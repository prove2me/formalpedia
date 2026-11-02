-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_triangulated_supergraph__p2m_a3a0b559_5297_496f_932d_5e752a281600_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:08:25.748318+00:00
-- url     : https://prove2.me/submissions/c940178a-4924-455d-a9fb-5c565dcf6750
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_planar_supergraph__p2m_9a3366a6_4a3c_4f33_8539_99f470118709_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_euler_edge_count__p2m_9a3366a6_4a3c_4f33_8539_99f470118709_a1
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V) :
    ∃ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      L <= M ∧ HasPlanarDrawingOn M ∧
        M.edgeFinset.card + 6 = 3 * Fintype.card V := by
  obtain ⟨M, dM, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.drawable_graph_has_maximal_planar_supergraph__p2m_9a3366a6_4a3c_4f33_8539_99f470118709_a1
      L dL hL hcard
  have hcount :=
    WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count__p2m_9a3366a6_4a3c_4f33_8539_99f470118709_a1
      M dM hM hcard hmax
  exact ⟨M, dM, hLM, hM, hcount⟩