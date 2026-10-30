-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulated_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:05:55.021184+00:00
-- url     : https://prove2.me/submissions/72850060-2fec-48a7-880a-e00820013285

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulated_extension_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_triangulated_extension_maximal_supergraph_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.planar_triangulated_extension_maximal_supergraph L hL
  have hedge :=
    WilliamsonShmoys.planar_triangulated_extension_maximal_supergraph_edge_count
      M hV hM hmax
  exact ⟨M, hLM, hM, hedge⟩