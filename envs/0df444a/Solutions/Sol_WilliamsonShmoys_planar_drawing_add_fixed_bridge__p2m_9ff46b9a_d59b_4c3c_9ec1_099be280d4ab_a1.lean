-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_fixed_bridge__p2m_9ff46b9a_d59b_4c3c_9ec1_099be280d4ab_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:27:47.328128+00:00
-- url     : https://prove2.me/submissions/492e786c-86e1-4fbe-8ae4-8a5ca2ff89a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_bridge_reachable_cut__p2m_016bc9c9_be0e_41b2_afe4_acfa54df6433_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_cut_bridge__p2m_016bc9c9_be0e_41b2_afe4_acfa54df6433_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    {u v : V}
    (hUnreachable : ¬ G.Reachable u v) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ HasPlanarDrawingOn K ∧ K.Adj u v := by
  obtain ⟨s, hu, hv, hcut⟩ :=
    WilliamsonShmoys.planar_bridge_reachable_cut__p2m_016bc9c9_be0e_41b2_afe4_acfa54df6433_a1
      G (u := u) (v := v) hUnreachable
  exact
    WilliamsonShmoys.planar_drawing_add_cut_bridge__p2m_016bc9c9_be0e_41b2_afe4_acfa54df6433_a1
      (G := G) (u := u) (v := v) hG s hu hv hcut
