-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_bound__p2m_f3f359af_2762_432f_8e05_8cdbcb14d938_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:15:47.196652+00:00
-- url     : https://prove2.me/submissions/9375a9c0-633a-47f1-bbe3-e030be958382

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_edge_completion__p2m_09fd82f6_9481_4fe8_ab66_93ef18097a0d_a5
import Theorems.Thm_WilliamsonShmoys_ncard_le_of_subset_card_eq__p2m_09fd82f6_9481_4fe8_ab66_93ef18097a0d_a5

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hsub, _hDrawH, hcard⟩ :=
    WilliamsonShmoys.exists_planar_edge_completion__p2m_09fd82f6_9481_4fe8_ab66_93ef18097a0d_a5
      G hDraw hCard
  exact WilliamsonShmoys.ncard_le_of_subset_card_eq__p2m_09fd82f6_9481_4fe8_ab66_93ef18097a0d_a5
    G.edgeSet H.edgeSet (3 * Fintype.card V - 6) hsub hcard