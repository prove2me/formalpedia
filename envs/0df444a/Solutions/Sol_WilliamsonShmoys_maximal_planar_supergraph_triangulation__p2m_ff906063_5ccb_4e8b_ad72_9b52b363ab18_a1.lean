-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_triangulation__p2m_ff906063_5ccb_4e8b_ad72_9b52b363ab18_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:57:53.104943+00:00
-- url     : https://prove2.me/submissions/53aff291-5193-48ef-9f51-3eb6536641ca

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal__p2m_3c9d29e6_223d_45fd_8079_57d4a2d204ad_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_3c9d29e6_223d_45fd_8079_57d4a2d204ad_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hconn : L.Connected)
    (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L <= M ∧ HasPlanarDrawingOn M ∧
      (letI : (G : SimpleGraph V) -> DecidableRel G.Adj :=
        fun G => Classical.decRel G.Adj
       M.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal__p2m_3c9d29e6_223d_45fd_8079_57d4a2d204ad_a1
      L hcard hconn hL
  exact ⟨M, hLM, hM,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_3c9d29e6_223d_45fd_8079_57d4a2d204ad_a1
      M hcard hM hmax⟩