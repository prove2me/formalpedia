-- Prove2me | solution 1 for WilliamsonShmoys.planar_underfull_edge_augmentation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:51:16.93392+00:00
-- url     : https://prove2.me/submissions/aa3752ff-251c-49d8-aa9b-22b47c7dc9ea

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_lower_bound

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hunderfull : G.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ M : SimpleGraph V,
      Set.Subset G.edgeSet M.edgeSet ∧
      M.edgeSet ≠ G.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M := by
  by_contra hno
  have hmax : ∀ M : SimpleGraph V,
      Set.Subset G.edgeSet M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M → M.edgeSet = G.edgeSet := by
    intro M hsub hM
    by_contra hne
    exact hno ⟨M, hsub, hne, hM⟩
  have hbound := WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound G hV hG hmax
  omega