-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_5b23b791_8f68_4090_90fa_7eb62c80871a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:56:01.59687+00:00
-- url     : https://prove2.me/submissions/c04fe748-355f-4685-bb58-c1ac271dcf2b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_32302080_d9f8_461c_9542_c9cd7d932e42_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_32302080_d9f8_461c_9542_c9cd7d932e42_a1
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V)
    (hR : HasPlanarDrawingOn R) (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ S : SimpleGraph V, R ≤ S → HasPlanarDrawingOn S → S = R) :
    ∀ [hRdec : DecidableRel R.Adj], R.edgeFinset.card + 6 = 3 * Fintype.card V := by
  intro hRdec
  have hupper := WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_32302080_d9f8_461c_9542_c9cd7d932e42_a1
    R hR hcard hmax
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_32302080_d9f8_461c_9542_c9cd7d932e42_a1
    R hR hcard hmax
  omega