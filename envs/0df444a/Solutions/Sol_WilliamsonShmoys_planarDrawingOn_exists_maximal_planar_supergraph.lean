-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_exists_maximal_planar_supergraph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:28:35.742197+00:00
-- url     : https://prove2.me/submissions/1c7e4f8d-0819-49e5-bc2c-eb2ef4fa926f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edgeMaximalPlanarSupergraphOn
import Theorems.Thm_WilliamsonShmoys_edgeMaximalPlanarOn_card

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.exists_edgeMaximalPlanarSupergraphOn M hV hM
  exact ⟨N, hMN, hN,
    WilliamsonShmoys.edgeMaximalPlanarOn_card N hV hN hmax⟩
