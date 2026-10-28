-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulation_extension_for_edge_bound_c61b3391
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:47:36.39415+00:00
-- url     : https://prove2.me/submissions/78d0ab88-304e-4225-801a-55db36767930
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_exists_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_c61b3391

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hKplanar, hKmax⟩ :=
    WilliamsonShmoys.planar_extension_exists_maximal_supergraph H hH
  exact ⟨K, hHK, hKplanar,
    WilliamsonShmoys.maximal_planar_edge_count_c61b3391 K hV hKplanar hKmax⟩