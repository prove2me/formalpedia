-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_2868a47b_b066_46c0_a57b_16dc6ed3b9ef_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:40:39.864768+00:00
-- url     : https://prove2.me/submissions/8ebf7a1a-0957-4f64-9804-fded7834e305
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_cross_component_edge__p2m_93892d71_84f1_4ed6_a896_c06ddcff432e_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_from_bridge_step__p2m_93892d71_84f1_4ed6_a896_c06ddcff432e_a2
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : HasPlanarDrawingOn G) (hconn : ¬ G.Connected) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by
  exact WilliamsonShmoys.planar_drawing_connected_extension_from_bridge_step__p2m_93892d71_84f1_4ed6_a896_c06ddcff432e_a2
    (fun X hXconn hXdraw =>
      WilliamsonShmoys.planar_drawing_add_cross_component_edge__p2m_93892d71_84f1_4ed6_a896_c06ddcff432e_a2
        X hXdraw hXconn)
    G hG hconn