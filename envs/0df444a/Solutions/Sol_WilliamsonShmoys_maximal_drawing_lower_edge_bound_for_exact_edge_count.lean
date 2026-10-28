-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_lower_edge_bound_for_exact_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:51:30.357983+00:00
-- url     : https://prove2.me/submissions/b684807c-5bce-44de-bcd7-604c811df717
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_lower_edge_count
import Theorems.Thm_WilliamsonShmoys_edge_count_eq_of_graph_equiv

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hLdraw, hLbound⟩ :=
    WilliamsonShmoys.planar_drawing_supergraph_lower_edge_count K hK hCard
  have hLK : L ≤ K := hmax L hKL hLdraw
  have hEq := WilliamsonShmoys.edge_count_eq_of_graph_equiv K L hKL hLK
  omega