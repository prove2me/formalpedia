-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_b17d3809_e307_4597_82b6_1d4f1ebd7e38_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T09:07:03.784996+00:00
-- url     : https://prove2.me/submissions/209cd02c-dc7a-4022-81e9-9f68bf2ccb3f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_ceffe8f7_0bd7_41ea_898f_3fe9bc8f26e2_a1
import Theorems.Thm_WilliamsonShmoys_subgraph_edgeSet_ncard_le__p2m_ceffe8f7_0bd7_41ea_898f_3fe9bc8f26e2_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hConn : P.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    P.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨Q, hPQ, hQDraw, hQCount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_ceffe8f7_0bd7_41ea_898f_3fe9bc8f26e2_a1
      P hDraw hConn hCard
  have hMono :=
    WilliamsonShmoys.subgraph_edgeSet_ncard_le__p2m_ceffe8f7_0bd7_41ea_898f_3fe9bc8f26e2_a1
      P Q hPQ
  rw [hQCount] at hMono
  exact hMono