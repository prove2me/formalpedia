-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_79b6cb48_7614_4e86_94da_1fe8fbba64b0_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:11:05.38117+00:00
-- url     : https://prove2.me/submissions/fb85df7f-9be1-42c0-b5ad-8f5677258234
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_edge_maximal_completion__p2m_c94121e2_adc9_4018_a433_d3dee737ddb5_a1
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_has_exact_edge_count__p2m_c94121e2_adc9_4018_a433_d3dee737ddb5_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKplanar, hKmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_edge_maximal_completion__p2m_c94121e2_adc9_4018_a433_d3dee737ddb5_a1
      H hplanar hV
  have hcount :=
    WilliamsonShmoys.edge_maximal_planar_graph_has_exact_edge_count__p2m_c94121e2_adc9_4018_a433_d3dee737ddb5_a1
      K hKplanar hV hKmax
  exact ⟨K, hHK, hKplanar, hcount⟩