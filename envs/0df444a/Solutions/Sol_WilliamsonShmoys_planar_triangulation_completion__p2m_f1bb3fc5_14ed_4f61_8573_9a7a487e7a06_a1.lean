-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_f1bb3fc5_14ed_4f61_8573_9a7a487e7a06_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:52:40.704967+00:00
-- url     : https://prove2.me/submissions/2cec6a8c-a04f-43e3-8965-d15a9953cf20

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_has_maximal_drawable_supergraph__p2m_fc475467_cefd_44fd_810b_5d1d49565f31_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_exact_edge_count__p2m_fc475467_cefd_44fd_810b_5d1d49565f31_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V - 6 = L.edgeSet.ncard := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_has_maximal_drawable_supergraph__p2m_fc475467_cefd_44fd_810b_5d1d49565f31_a1 K hK
  refine ⟨L, hKL, hL, ?_⟩
  exact WilliamsonShmoys.maximal_drawable_graph_exact_edge_count__p2m_fc475467_cefd_44fd_810b_5d1d49565f31_a1 L hV hL hmax