-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_augmentation_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:22:42.669629+00:00
-- url     : https://prove2.me/submissions/1e4837c8-e568-4a2a-9395-2cfbdb765365

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_maximal_extension
import Theorems.Thm_WilliamsonShmoys_planar_maximal_drawing_edge_lower_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V,
      J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  obtain ⟨K, hJK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_augmentation_maximal_extension J hJ
  exact ⟨K, hJK, hK,
    WilliamsonShmoys.planar_maximal_drawing_edge_lower_bound K hV hK hmax⟩