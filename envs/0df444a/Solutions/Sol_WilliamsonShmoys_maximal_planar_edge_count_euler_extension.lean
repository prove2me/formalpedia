-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_euler_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T03:24:42.495754+00:00
-- url     : https://prove2.me/submissions/4d94d120-beed-4458-8cb0-3354f7b661c4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_same_vertices_repair3_179e6262
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_euler_repair3_179e6262

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ J : SimpleGraph V, H ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J ∧
      J.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨J, hHJ, hJ, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_same_vertices_repair3_179e6262 H hH
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count_euler_repair3_179e6262 J hJ hMax hCard
  exact ⟨J, hHJ, hJ, hCount⟩