-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_bridge_step__p2m_b76599c1_0a89_4269_bf03_ff901f7f247a_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:50:11.679419+00:00
-- url     : https://prove2.me/submissions/aef91df6-85cb-403e-be0e-5989f53ee2e1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_vertices_exist__p2m_399eeee6_4234_4eb0_9aa5_260fcba2f92a_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_between_components__p2m_399eeee6_4234_4eb0_9aa5_260fcba2f92a_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 0 < Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ ∀ u v, Relation.ReflTransGen G.Adj u v) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∃ u v, ¬ Relation.ReflTransGen G.Adj u v ∧ H.Adj u v := by
  obtain ⟨u, v, huv⟩ :=
    WilliamsonShmoys.disconnected_vertices_exist__p2m_399eeee6_4234_4eb0_9aa5_260fcba2f92a_a1
      G hV hDisconnected
  obtain ⟨H, hGH, hH, huvEdge⟩ :=
    WilliamsonShmoys.planar_drawing_bridge_between_components__p2m_399eeee6_4234_4eb0_9aa5_260fcba2f92a_a1
      G u v hG huv
  exact ⟨H, hGH, hH, u, v, huv, huvEdge⟩