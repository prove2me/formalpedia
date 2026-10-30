-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_5172cebe_7d77_4b25_aa7c_10802cca0895_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:49:24.767124+00:00
-- url     : https://prove2.me/submissions/9cfd9064-0d5d-44ee-b5d9-ebf1cda958f9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_e3290709_cdc2_4958_9fab_02f715f97993_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_simple_graph_edge_lower_bound__p2m_e3290709_cdc2_4958_9fab_02f715f97993_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_e3290709_cdc2_4958_9fab_02f715f97993_a2 H hH hcard
  · exact WilliamsonShmoys.maximal_planar_simple_graph_edge_lower_bound__p2m_e3290709_cdc2_4958_9fab_02f715f97993_a2 H hH hmax hcard