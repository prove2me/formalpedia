-- Prove2me | solution 1 for WilliamsonShmoys.planar_augmentation_to_maximal_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:19:13.153732+00:00
-- url     : https://prove2.me/submissions/31441288-8ef1-4fc2-97ca-96f0d48071d3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_exists_maximal
import Theorems.Thm_WilliamsonShmoys_maximal_planar_has_maximal_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_augmentation_exists_maximal K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_planar_has_maximal_edge_count L hV hL hmax⟩