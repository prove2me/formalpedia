-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulation__p2m_75785758_9f27_4736_ab49_77b09febfcc3_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:33:28.220729+00:00
-- url     : https://prove2.me/submissions/5babe888-d16f-4707-aa09-1c337248100a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal__p2m_43831d01_c2a2_47cc_baf7_12299ab7bdf8_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_43831d01_c2a2_47cc_baf7_12299ab7bdf8_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V, K <= H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      3 * Fintype.card V = H.edgeSet.ncard + 6 := by
  obtain ⟨H, hKH, hH, hmax⟩ := WilliamsonShmoys.planar_supergraph_maximal__p2m_43831d01_c2a2_47cc_baf7_12299ab7bdf8_a1 K hK hV
  exact ⟨H, hKH, hH, WilliamsonShmoys.maximal_planar_edge_count__p2m_43831d01_c2a2_47cc_baf7_12299ab7bdf8_a1 H hH hV hmax⟩
