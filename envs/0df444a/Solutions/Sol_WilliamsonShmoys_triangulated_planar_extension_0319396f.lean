-- Prove2me | solution 1 for WilliamsonShmoys.triangulated_planar_extension_0319396f
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:33:20.923449+00:00
-- url     : https://prove2.me/submissions/4f248cd2-d461-40ce-8459-9e206d7aa5d1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_0319396f

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_edge_count_0319396f K hK hmax hV⟩