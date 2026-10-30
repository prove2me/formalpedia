-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_edge_count_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:24:28.936922+00:00
-- url     : https://prove2.me/submissions/5c323d06-317d-4da3-a0e5-2274ef422958

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_planar_sparse_graph_has_planar_edge_augmentation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  by_contra hgoal
  have hsparse : L.edgeSet.ncard + 6 < 3 * Fintype.card V := by omega
  obtain ⟨M, hLM, hM, hneq⟩ :=
    WilliamsonShmoys.planar_sparse_graph_has_planar_edge_augmentation L hV hL hsparse
  exact hneq (hmax M hLM hM)

