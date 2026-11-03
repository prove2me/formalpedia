-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_4f438a2b_7c24_414a_8cb6_3aa4d799f4d5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T05:16:03.500191+00:00
-- url     : https://prove2.me/submissions/699f68c0-3c49-4bb9-bd1b-a4ca9ddb8e8f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_for_edge_bound_target
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_count__p2m_8c5f7fcd_4410_4b31_b397_bfdf744b7888_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     letI : Fintype ↑G.edgeSet := Fintype.ofFinite _
     G.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  classical
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension_for_edge_bound_target G hG
  letI : Fintype ↑G.edgeSet := Fintype.ofFinite _
  have hle : G.edgeFinset.card ≤ H.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hGH)
  have heq : H.edgeFinset.card + 6 = 3 * Fintype.card V :=
    WilliamsonShmoys.maximal_planar_euler_count__p2m_8c5f7fcd_4410_4b31_b397_bfdf744b7888_a2 H hH hmax hV
  omega
