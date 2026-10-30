-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension_edge_count__p2m_adaa59b8_bbaf_4393_8e55_4a0450b92ec8_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:53:06.855474+00:00
-- url     : https://prove2.me/submissions/9d5b2b96-e289-49bc-93f4-0ad7d42ddd73
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_extension__p2m_b6eb2a76_7845_4b9d_82ab_24d9043bea47_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_b6eb2a76_7845_4b9d_82ab_24d9043bea47_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      HasPlanarDrawingOn N ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hN, hCardMono, hMax⟩ :=
    WilliamsonShmoys.finite_maximal_planar_extension__p2m_b6eb2a76_7845_4b9d_82ab_24d9043bea47_a1
      M hM hCard
  exact ⟨N, hMN, hN, hCardMono,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_b6eb2a76_7845_4b9d_82ab_24d9043bea47_a1
      N hN hCard hMax⟩