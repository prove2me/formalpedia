-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:10:00.475133+00:00
-- url     : https://prove2.me/submissions/6d34088f-2bbc-4060-9778-bcd682744dbc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_for_job_3a7ba4e8_8a44_4d12_bfa9_d180fa091eca

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V,
      M ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hMH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_drawable_maximal_supergraph M hM
  exact ⟨H, hMH, hH,
    WilliamsonShmoys.maximal_drawable_edge_count_for_job_3a7ba4e8_8a44_4d12_bfa9_d180fa091eca
      H hV hH hmax⟩