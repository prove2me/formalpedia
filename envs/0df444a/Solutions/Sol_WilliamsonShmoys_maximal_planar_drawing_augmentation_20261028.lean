-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_augmentation_20261028
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:37:40.704441+00:00
-- url     : https://prove2.me/submissions/366430d6-3680-4ede-8cef-4b044663b385

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_maximal_extension_exists_20261028
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_maximal_edge_count_20261028

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_maximal_extension_exists_20261028 G hG
  exact ⟨K, hGK, hK,
    WilliamsonShmoys.maximal_planar_drawing_maximal_edge_count_20261028 K hK hCard hmax⟩