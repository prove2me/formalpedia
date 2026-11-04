-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_components_reduce_edge_bound__p2m_fab89fb1_e873_4b82_98f3_cd1985d7426b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:37:17.90957+00:00
-- url     : https://prove2.me/submissions/cbf998af-9719-473a-8683-c8a03192b7c7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_component_reduction__p2m_263e0430_0bed_4695_a55f_33a5be744a5b_a1
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hPlanar : HasPlanarDrawingOn K)
    (hConnectedBound :
      ∀ {W : Type} [Fintype W] [LinearOrder W] (G : SimpleGraph W),
        3 ≤ Fintype.card W → G.Connected → HasPlanarDrawingOn G →
          (letI : DecidableRel G.Adj := Classical.decRel G.Adj
           G.edgeFinset.card + 6 ≤ 3 * Fintype.card W)) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    K.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  exact WilliamsonShmoys.planar_drawing_edge_upper_bound_component_reduction__p2m_263e0430_0bed_4695_a55f_33a5be744a5b_a1 K hV hPlanar hConnectedBound
