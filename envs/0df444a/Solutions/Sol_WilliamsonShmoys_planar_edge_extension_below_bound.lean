-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_extension_below_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:44:17.672956+00:00
-- url     : https://prove2.me/submissions/d97f0d8c-d07b-4d58-9ec5-6c236b324385

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_bound_of_drawing_maximal

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcount : G.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ S : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn S ∧
      Set.Subset G.edgeSet S.edgeSet ∧
      S.edgeSet ≠ G.edgeSet := by
  by_contra htarget
  have hmax :
      ∀ S : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn S →
        G.edgeSet ⊆ S.edgeSet →
        G.edgeSet = S.edgeSet := by
    intro S hS hsub
    by_contra hnot
    apply htarget
    refine ⟨S, hS, hsub, ?_⟩
    intro heq
    exact hnot heq.symm
  have hb :=
    WilliamsonShmoys.edge_bound_of_drawing_maximal
      G hCard hG hmax
  omega