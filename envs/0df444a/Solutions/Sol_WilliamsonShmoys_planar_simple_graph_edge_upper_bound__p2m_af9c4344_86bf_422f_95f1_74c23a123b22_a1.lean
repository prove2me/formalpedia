-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_af9c4344_86bf_422f_95f1_74c23a123b22_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:46:33.051119+00:00
-- url     : https://prove2.me/submissions/d2dcfc1e-1775-48ed-8025-794d80606b5a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extends_to_triangulation__p2m_e13857bb_dfd7_4e7a_a1e7_eab5feffe183_a3
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) [DecidableRel L.Adj]
    (hL : HasPlanarDrawingOn L) (hcard : 3 ≤ Fintype.card V) :
    L.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, dH, h⟩ :=
    WilliamsonShmoys.planar_drawing_extends_to_triangulation__p2m_e13857bb_dfd7_4e7a_a1e7_eab5feffe183_a3
      L hL hcard
  letI : DecidableRel H.Adj := dH
  obtain ⟨hsub, _hdraw, htri⟩ := h
  calc
    L.edgeFinset.card + 6 ≤ H.edgeFinset.card + 6 :=
      Nat.add_le_add_right (Finset.card_le_card hsub) 6
    _ = 3 * Fintype.card V := htri