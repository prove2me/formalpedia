-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_08c24848_031b_43ea_aa26_092fb49494c8_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T16:15:14.512082+00:00
-- url     : https://prove2.me/submissions/4e45da9b-e5f9-481d-be02-6c27cf9dbc10

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_c26dc073_3bb3_419b_aef0_cb3d89286f37_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    (letI : (G : SimpleGraph V) → DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
     M.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  letI : (G : SimpleGraph V) → DecidableRel G.Adj :=
    fun G => Classical.decRel G.Adj
  have h := WilliamsonShmoys.planar_drawing_edge_bound__p2m_c26dc073_3bb3_419b_aef0_cb3d89286f37_a1 M hcard hM
  exact Nat.le_sub_of_add_le h