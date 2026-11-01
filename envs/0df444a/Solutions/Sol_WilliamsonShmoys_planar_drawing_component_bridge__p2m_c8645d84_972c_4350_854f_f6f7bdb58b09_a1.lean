-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_component_bridge__p2m_c8645d84_972c_4350_854f_f6f7bdb58b09_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:46:07.105212+00:00
-- url     : https://prove2.me/submissions/cddf927d-7581-4096-bf62-85f43768be16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_disconnected_supergraph_bridge__p2m_b2249a9b_0ed4_4e0a_b974_67058e424e5f_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V)
    (hdis : ¬ G.Connected) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v := by
  exact WilliamsonShmoys.planar_disconnected_supergraph_bridge__p2m_b2249a9b_0ed4_4e0a_b974_67058e424e5f_a1 G hG hdis