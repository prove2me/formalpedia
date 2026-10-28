-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_extension_edge_bound_a9d6da29_ff69_465c_9a71_ac972a1190c4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:31:17.517013+00:00
-- url     : https://prove2.me/submissions/e31b4cf7-648e-4c1b-9e8f-8798da8665d3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_818bf149_0bfd_4348_866a_626aa910ef08
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_818bf149_0bfd_4348_866a_626aa910ef08

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V,
      M ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨T, hMT, hT, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension_818bf149_0bfd_4348_866a_626aa910ef08 M hM hV
  exact ⟨T, hMT, hT,
    WilliamsonShmoys.maximal_planar_edge_count_818bf149_0bfd_4348_866a_626aa910ef08 T hT hmax hV⟩