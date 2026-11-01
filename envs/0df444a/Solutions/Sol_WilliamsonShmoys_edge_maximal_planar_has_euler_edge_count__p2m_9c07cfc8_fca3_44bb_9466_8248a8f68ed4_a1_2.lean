-- Prove2me | solution 2 for WilliamsonShmoys.edge_maximal_planar_has_euler_edge_count__p2m_9c07cfc8_fca3_44bb_9466_8248a8f68ed4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:13:12.133691+00:00
-- url     : https://prove2.me/submissions/437eabcf-dac5-435c-a5bf-9264610cf462

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_supergraph_93a36477_a46b_4b11_b4cb_7379952edbbc

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M) (hcard : 3 ≤ Fintype.card V) (hmax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) : 3 * Fintype.card V = M.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_planar_edge_count_for_supergraph_93a36477_a46b_4b11_b4cb_7379952edbbc M hcard hplanar hmax
