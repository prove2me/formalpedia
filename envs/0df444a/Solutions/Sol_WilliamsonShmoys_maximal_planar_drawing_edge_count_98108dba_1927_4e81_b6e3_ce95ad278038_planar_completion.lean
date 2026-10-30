-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_98108dba_1927_4e81_b6e3_ce95ad278038_planar_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:33:57.092109+00:00
-- url     : https://prove2.me/submissions/db9a40b8-e050-4f61-950f-588373e82309

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_2a77893c_8379_4827_8265_76a9c861f3f2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count_2a77893c_8379_4827_8265_76a9c861f3f2
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_2a77893c_8379_4827_8265_76a9c861f3f2 L hV hL
  exact ⟨M, hLM, hM,
    WilliamsonShmoys.maximal_planar_supergraph_edge_count_2a77893c_8379_4827_8265_76a9c861f3f2 M hV hM hmax⟩