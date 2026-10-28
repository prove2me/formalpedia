-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_with_maximal_edge_count_b2facf4f_375b_4f83_ba19_34094f723a5d
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:48:13.988661+00:00
-- url     : https://prove2.me/submissions/52b8a4ad-488d-4e43-b6ce-24ebff8d806f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_ec05fb32_d087_4cea_a2cd_8a3ca91ed513
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_ec05fb32_d087_4cea_a2cd_8a3ca91ed513

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V = N.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph_ec05fb32_d087_4cea_a2cd_8a3ca91ed513 M hM
  exact ⟨N, hMN, hN,
    WilliamsonShmoys.maximal_planar_edge_count_ec05fb32_d087_4cea_a2cd_8a3ca91ed513 N hV hN hmax⟩