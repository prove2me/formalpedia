-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_augmentation_6c0819c8_795c_411a_aacd_f8cf4c691759
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:30:41.100695+00:00
-- url     : https://prove2.me/submissions/df357c35-12f8-4bb9-b733-d0732b127823
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_supergraph_for_edge_lower_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count_for_edge_lower_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ U : SimpleGraph V,
      HasPlanarDrawingOn U ∧
      (∀ u v, T.Adj u v → U.Adj u v) ∧
      3 * Fintype.card V ≤ U.edgeSet.ncard + 6 := by
  obtain ⟨U, hU, hTU, hMax⟩ :=
    WilliamsonShmoys.planar_drawingOn_maximal_supergraph_for_edge_lower_bound T hT
  have hCount :=
    WilliamsonShmoys.maximal_planar_drawingOn_edge_count_for_edge_lower_bound
      U hU hMax hCard
  exact ⟨U, hU, hTU, le_of_eq hCount⟩