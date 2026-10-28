-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_maximizing_edges
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:39:42.499014+00:00
-- url     : https://prove2.me/submissions/edebb864-643c-4653-bfeb-e5268e9d62cc

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        L ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N →
        N.edgeSet.ncard ≤ M.edgeSet.ncard := by 
  classical
  obtain ⟨M, hM, hmax⟩ := Set.exists_max_image
    {N : SimpleGraph V | L ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N}
    (fun N => N.edgeSet.ncard) (Set.toFinite _) ⟨L, le_rfl, hL⟩
  exact ⟨M, hM.1, hM.2, fun N h1 h2 => hmax N ⟨h1, h2⟩⟩
