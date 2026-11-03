-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_32302080_d9f8_461c_9542_c9cd7d932e42_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:17:01.674474+00:00
-- url     : https://prove2.me/submissions/b6bde35a-21f4-4298-99a6-6f017300bca6

import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_drawing__p2m_bc188a74_c743_4521_84db_ff6e1b478f87_a1

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V) (hR : HasPlanarDrawingOn R) (hcard : 3 ≤ Fintype.card V) (hmax : ∀ S : SimpleGraph V, R ≤ S → HasPlanarDrawingOn S → S = R) : ∀ [hRdec : DecidableRel R.Adj], R.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  intro hRdec
  exact WilliamsonShmoys.planar_edge_bound_from_drawing__p2m_bc188a74_c743_4521_84db_ff6e1b478f87_a1 R hR hcard