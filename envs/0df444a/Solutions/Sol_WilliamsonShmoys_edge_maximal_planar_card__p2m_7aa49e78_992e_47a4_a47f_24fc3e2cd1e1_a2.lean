-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_card__p2m_7aa49e78_992e_47a4_a47f_24fc3e2cd1e1_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:19:59.100596+00:00
-- url     : https://prove2.me/submissions/4c48c52a-e52b-42c8-8b41-512fb487ee72
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_26401141_9acd_45a7_9799_c63f2391b494_a2__p2m_26401141_9acd_45a7_9799_c63f2391b494_a3
import Theorems.Thm_WilliamsonShmoys_planar_strict_extension_below_max__p2m_26401141_9acd_45a7_9799_c63f2391b494_a2__p2m_26401141_9acd_45a7_9799_c63f2391b494_a3

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    (∀ H : SimpleGraph V,
      G.edgeFinset ⊆ H.edgeFinset →
      HasPlanarDrawingOn H →
      H.edgeFinset ⊆ G.edgeFinset) →
    G.edgeFinset.card = 3 * Fintype.card V - 6 := by
  classical
  letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
    fun G => Classical.decRel G.Adj
  intro hmax
  have hupper :
      G.edgeFinset.card ≤ 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.planar_edge_count_upper_bound__p2m_26401141_9acd_45a7_9799_c63f2391b494_a2__p2m_26401141_9acd_45a7_9799_c63f2391b494_a3
      G hG hcard
  by_contra hneq
  have hlt :
      G.edgeFinset.card < 3 * Fintype.card V - 6 := by
    omega
  obtain ⟨H, hsub, hdraw, hnotrev⟩ :=
    WilliamsonShmoys.planar_strict_extension_below_max__p2m_26401141_9acd_45a7_9799_c63f2391b494_a2__p2m_26401141_9acd_45a7_9799_c63f2391b494_a3
      G hG hcard hlt
  exact hnotrev (hmax H hsub hdraw)