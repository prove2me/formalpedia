-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulated_completion_30a2cd75
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T14:03:27.191015+00:00
-- url     : https://prove2.me/submissions/03ec41db-6a30-4420-8eb8-4fe849bf3d86

import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_730ed87f_4857_4202_bf37_5fbad1be2596
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_730ed87f_4857_4202_bf37_5fbad1be2596

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V, M ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨T, hMT, hT, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_730ed87f_4857_4202_bf37_5fbad1be2596 M hM
  refine ⟨T, hMT, hT, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_edge_count_730ed87f_4857_4202_bf37_5fbad1be2596 T hV hT hmax