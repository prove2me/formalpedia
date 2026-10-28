-- Prove2me | solution 1 for WilliamsonShmoys.planar_sparse_graph_extendible
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:29:36.960392+00:00
-- url     : https://prove2.me/submissions/976ae5e1-2ab1-4f30-bc1a-4e9920553291
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_exact_edge_count

set_option autoImplicit false

/-- The maximal planar completion theorem gives a strict drawable extension. -/
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hsparse : H.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧ ¬ K.edgeSet ⊆ H.edgeSet := by
  obtain ⟨K, hHK, hK, hcard, hstrict⟩ :=
    WilliamsonShmoys.planar_completion_exact_edge_count H hV hH hsparse
  exact ⟨K, hHK, hK, hstrict⟩