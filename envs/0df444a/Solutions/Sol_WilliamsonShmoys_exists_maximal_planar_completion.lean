-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:09:11.720177+00:00
-- url     : https://prove2.me/submissions/ccff3a91-7c3b-422a-af1c-e53495976453

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_completion_supergraph
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_completion

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_completion_supergraph G hG
  have hcount := WilliamsonShmoys.edge_count_of_maximal_planar_completion
    H hV hH hmax
  exact ⟨H, hGH, hH, hmax, hcount⟩