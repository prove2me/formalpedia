-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_f3a63840_9387_418b_904c_fbe2e8408361_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T16:13:01.324951+00:00
-- url     : https://prove2.me/submissions/0f00f185-0cce-4771-8652-5b63ecc2e3f3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_card_upper_bound__p2m_26140456_b7e4_4d83_b9c1_39ddc27ba139_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hconnected : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    letI : (G : SimpleGraph V) → DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  letI : (G : SimpleGraph V) → DecidableRel G.Adj := fun G => Classical.decRel G.Adj
  exact WilliamsonShmoys.planar_edge_card_upper_bound__p2m_26140456_b7e4_4d83_b9c1_39ddc27ba139_a1 K hdraw hcard

