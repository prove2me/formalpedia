-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_triangulation_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:37:15.566398+00:00
-- url     : https://prove2.me/submissions/ef2b4027-2741-4f58-aa9c-c667bc3f45e3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_exists_repair3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_repair3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V,
      HasPlanarDrawingOn T ∧
      (∀ u v, G.Adj u v → T.Adj u v) ∧
      T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨T, hT, hGT, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_exists_repair3 G hdraw
  exact ⟨T, hT, hGT,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_repair3 T hT hCard hmax⟩