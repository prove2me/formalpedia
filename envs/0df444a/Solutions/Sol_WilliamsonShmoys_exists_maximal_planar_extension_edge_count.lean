-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_extension_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:26:51.242046+00:00
-- url     : https://prove2.me/submissions/b1414a53-fbb5-4a91-b952-281ff558331e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_for_edge_count
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_of_maximal_extension
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension_for_edge_count H hH
  refine ⟨K, hHK, hK, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count_of_maximal_extension K hV hK hmax