-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_completion_ed91fffc_a32b_46e0_9209_f57c29a4258c
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:53:26.959191+00:00
-- url     : https://prove2.me/submissions/b4ca9c32-34df-4a32-906c-1ac3057fc4c2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_completion_ed91fffc_a32b_46e0_9209_f57c29a4258c_finite_maximal_extension
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_completion_ed91fffc_a32b_46e0_9209_f57c29a4258c_maximal_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G <= K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_edge_count_completion_ed91fffc_a32b_46e0_9209_f57c29a4258c_finite_maximal_extension G hG
  exact ⟨K, hGK, hK,
    WilliamsonShmoys.planar_drawing_edge_count_completion_ed91fffc_a32b_46e0_9209_f57c29a4258c_maximal_edge_count K hV hK hmax⟩