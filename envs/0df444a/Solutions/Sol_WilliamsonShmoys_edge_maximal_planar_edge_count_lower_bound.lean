-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_edge_count_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:13:48.731986+00:00
-- url     : https://prove2.me/submissions/b4821a2f-0485-45c0-afd4-c8b66388c3a7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count_bound
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet ⊆ H.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hK, hBound⟩ :=
    WilliamsonShmoys.planar_completion_edge_count_bound H hH hCard
  have hKH : K.edgeSet ⊆ H.edgeSet := hMax K hHK hK
  have hEq : K.edgeSet = H.edgeSet := Set.Subset.antisymm hKH hHK
  simpa [hEq] using hBound