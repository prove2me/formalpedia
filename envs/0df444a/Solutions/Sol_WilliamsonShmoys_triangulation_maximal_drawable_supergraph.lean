-- Prove2me | solution 1 for WilliamsonShmoys.triangulation_maximal_drawable_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:12:48.937245+00:00
-- url     : https://prove2.me/submissions/0b22fe92-f224-4ea4-a94b-1efb5c46f80e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_subgraph
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_hereditary

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      Set.Subset K.edgeSet L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        Set.Subset L.edgeSet M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet = L.edgeSet := by
  have hHereditary :
      ∀ G H : SimpleGraph V,
        Set.Subset G.edgeSet H.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn H →
        WilliamsonShmoys.HasPlanarDrawingOn G := by
    intro G H hGH hH
    exact WilliamsonShmoys.hasPlanarDrawingOn_subgraph hGH hH
  obtain ⟨L, hKL, hL, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_supergraph_of_hereditary
      (P := WilliamsonShmoys.HasPlanarDrawingOn) hHereditary K hK
  exact ⟨L, hKL, hL, hMax⟩
