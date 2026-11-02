-- Prove2me | solution 1 for WilliamsonShmoys.planar_add_bridge_between_disconnected_vertices__p2m_05c1a0b4_69ca_4d36_9f49_0774601d7f45_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:43:41.58434+00:00
-- url     : https://prove2.me/submissions/217b07b0-7bad-433b-8d22-9c187af84a6c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_bridge_curve_for_disconnected_vertices__p2m_3dd48983_b264_4c3c_82a7_94630b56a533_a3
import Theorems.Thm_WilliamsonShmoys_planar_add_edge_from_bridge_curve__p2m_3dd48983_b264_4c3c_82a7_94630b56a533_a3
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    {u v : V} (hnot : ¬ G.Reachable u v) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧ K.Adj u v := by
  obtain ⟨p, arc, gamma, ⟨hp, hedge, hdisjoint⟩, hcont, hinj, hstart, hend,
      hvertices, hedge_intersections⟩ :=
    WilliamsonShmoys.planar_bridge_curve_for_disconnected_vertices__p2m_3dd48983_b264_4c3c_82a7_94630b56a533_a3
      G hG hnot
  exact WilliamsonShmoys.planar_add_edge_from_bridge_curve__p2m_3dd48983_b264_4c3c_82a7_94630b56a533_a3
    G p arc gamma hp hedge hdisjoint hcont hinj hstart hend hvertices hedge_intersections