-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_triangulation_edge_count_maximal_drawable_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:50:04.732055+00:00
-- url     : https://prove2.me/submissions/77591788-0ad2-49f5-b185-5fbe53e688cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_for_maximal_drawable
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_for_maximal_drawable

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hup := WilliamsonShmoys.planar_edge_upper_bound_for_maximal_drawable T hT hV
  have hnot : ¬ T.edgeSet.ncard < 3 * Fintype.card V - 6 := by
    intro hgap
    obtain ⟨U, hTU, hne, hU⟩ :=
      WilliamsonShmoys.planar_edge_augmentation_for_maximal_drawable T hT hV hgap
    have hEq := hmax U hTU hU
    exact hne hEq
  omega