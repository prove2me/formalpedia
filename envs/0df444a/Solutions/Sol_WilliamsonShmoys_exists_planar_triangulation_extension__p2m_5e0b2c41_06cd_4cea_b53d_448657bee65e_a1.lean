-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_extension__p2m_5e0b2c41_06cd_4cea_b53d_448657bee65e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:50:17.469207+00:00
-- url     : https://prove2.me/submissions/b4a7d430-718a-4851-ba9f-917a0821c677
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_724aac7b_31c9_4291_9b6d_4edefcb29b4d_a1
import Theorems.Thm_WilliamsonShmoys_inclusion_maximal_planar_edge_count__p2m_724aac7b_31c9_4291_9b6d_4edefcb29b4d_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : G.Connected) :
    ∃ (H : SimpleGraph V), ∃ (dH : DecidableRel H.Adj),
      HasPlanarDrawingOn H ∧ G ≤ H ∧
        (letI : DecidableRel H.Adj := dH
         H.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  obtain ⟨H, dH, hH, hGH, hmax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_724aac7b_31c9_4291_9b6d_4edefcb29b4d_a1 G hG
  refine ⟨H, dH, hH, hGH, ?_⟩
  letI : DecidableRel H.Adj := dH
  exact WilliamsonShmoys.inclusion_maximal_planar_edge_count__p2m_724aac7b_31c9_4291_9b6d_4edefcb29b4d_a1 H hH hcard hmax