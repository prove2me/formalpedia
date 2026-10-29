-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound_retry_2cbac039
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T00:27:07.113992+00:00
-- url     : https://prove2.me/submissions/e8f41c00-b12a-4e68-a3a8-4749a71c9ac9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_retry_2cbac039_augment

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn M →
      L.edgeSet ⊆ M.edgeSet → M.edgeSet = L.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  by_contra h
  have hSparse : L.edgeSet.ncard + 6 < 3 * Fintype.card V := by omega
  obtain ⟨M, hM, hsub, hneq⟩ :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound_retry_2cbac039_augment
      L hL hCard hSparse
  have hback : M.edgeSet ⊆ L.edgeSet := by
    rw [hMax M hM hsub]
  exact hneq hback