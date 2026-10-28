-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_has_exact_edge_count_from_planarity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:33:27.335821+00:00
-- url     : https://prove2.me/submissions/474d150f-6757-419d-8683-8b12a71ae336
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_supergraph

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hHmax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet → H.edgeSet ≠ K.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn K) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKdraw, hKcount⟩ :=
    WilliamsonShmoys.planar_drawing_has_exact_edge_count_supergraph
      H hHdraw hCard
  have hEq : H.edgeSet = K.edgeSet := by
    by_contra hne
    exact (hHmax K hHK hne) hKdraw
  simpa [hEq] using hKcount