-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_edge_count_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:49:04.4625+00:00
-- url     : https://prove2.me/submissions/ba903347-1fe2-4903-b878-9aa3323f871e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_v2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_v2
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_maximal_extension_v2 H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_edge_bound_v2 K hK hmax hCard⟩
