-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_c3c9ffa7_0ab4_4781_8a7b_d6d91ceb974a_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:30:04.944521+00:00
-- url     : https://prove2.me/submissions/5fa82fd8-1a79-482c-8be8-f41fe61b6433
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_d8025907_d5c3_4b74_a462_234358441f90_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_exact_edge_count__p2m_d8025907_d5c3_4b74_a462_234358441f90_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 <= Fintype.card V) :
    Exists fun (L : SimpleGraph V) => Exists fun (dL : DecidableRel L.Adj) =>
      WilliamsonShmoys.HasPlanarDrawingOn L /\
      K.edgeFinset ⊆ L.edgeFinset /\
      L.edgeFinset.card = 3 * Fintype.card V - 6 := by
  obtain ⟨L, dL, hL, hsub, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_d8025907_d5c3_4b74_a462_234358441f90_a1
      K dK hK
  refine ⟨L, dL, hL, hsub, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_d8025907_d5c3_4b74_a462_234358441f90_a1
    L dL hL hn hmax