-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:16:04.100913+00:00
-- url     : https://prove2.me/submissions/7ede49c1-0181-47f0-a8bd-0d657e9b05eb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_drawable_supergraph_completion
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_triangulation_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      T ≤ K ∧ HasPlanarDrawingOn K ∧
        K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hTK, hK, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_drawable_supergraph_completion T hT
  refine ⟨K, hTK, hK, ?_⟩
  exact WilliamsonShmoys.maximal_drawable_graph_triangulation_edge_count K hK hmax hV
