-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_augment_to_maximal_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:24:44.427402+00:00
-- url     : https://prove2.me/submissions/bb9cf96c-2348-41ee-b424-a620618801fb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_exists_maximal_supergraph_e1b54b32
import Theorems.Thm_WilliamsonShmoys_maximalPlanarDrawingOn_edge_count_e1b54b32

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.planarDrawingOn_exists_maximal_supergraph_e1b54b32 M hM hV
  exact ⟨N, hMN, hN,
    WilliamsonShmoys.maximalPlanarDrawingOn_edge_count_e1b54b32 N hN hV hmax⟩