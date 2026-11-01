-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_has_triangulated_edge_count__p2m_7235810a_9787_44ff_bc97_6b6cda77c472_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:01:08.237418+00:00
-- url     : https://prove2.me/submissions/32b45f14-94d6-4e63-bc96-a06b6e54f454
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_of_drawing__p2m_d750730e_2711_4e55_8b38_5f4dbc12a87a_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_if_below_triangulated_bound__p2m_d750730e_2711_4e55_8b38_5f4dbc12a87a_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : HasPlanarDrawingOn W)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ X : SimpleGraph V, W ≤ X → HasPlanarDrawingOn X → X ≤ W) :
    letI : DecidableRel W.Adj := Classical.decRel W.Adj
    W.edgeFinset.card = 3 * Fintype.card V - 6 := by
  letI : DecidableRel W.Adj := Classical.decRel W.Adj
  have hupper := WilliamsonShmoys.planar_edge_upper_bound_of_drawing__p2m_d750730e_2711_4e55_8b38_5f4dbc12a87a_a1 W hW hcard
  by_contra hne
  have hlt : W.edgeFinset.card < 3 * Fintype.card V - 6 := by omega
  obtain ⟨X, hWX, hXne, hXplanar⟩ := WilliamsonShmoys.planar_edge_augmentation_if_below_triangulated_bound__p2m_d750730e_2711_4e55_8b38_5f4dbc12a87a_a1 W hW hcard hlt
  have hXW : X ≤ W := hmax X hWX hXplanar
  exact hXne (le_antisymm hXW hWX)