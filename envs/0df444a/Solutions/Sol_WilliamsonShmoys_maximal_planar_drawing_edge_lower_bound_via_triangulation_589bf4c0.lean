-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_via_triangulation_589bf4c0
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:13:44.116814+00:00
-- url     : https://prove2.me/submissions/8ef2e00a-79c0-4ae8-bf87-38ae425f607f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_if_sparse

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  by_contra hbound
  have hsparse : L.edgeSet.ncard + 6 < 3 * Fintype.card V := by omega
  obtain ⟨M, hLM, hMdraw, hnotML⟩ :=
    WilliamsonShmoys.planar_edge_augmentation_if_sparse
      L hV hL hsparse
  exact hnotML (hmax M hLM hMdraw)