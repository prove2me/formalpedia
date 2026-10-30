-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_ffc13159_3620_43e0_97b9_474801033c8c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:12:16.619514+00:00
-- url     : https://prove2.me/submissions/a45d3caa-a2e9-488b-9354-66d619d3b0e4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_max_pair_count__p2m_bb57e846_d9a4_493d_944c_0498086a1fa4_a3
import Theorems.Thm_WilliamsonShmoys_pair_count_strict_of_strict_subgraph__p2m_bb57e846_d9a4_493d_944c_0498086a1fa4_a3
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ L : SimpleGraph V, H ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L := by
  obtain ⟨L, hHL, hLDraw, hmax⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_max_pair_count__p2m_bb57e846_d9a4_493d_944c_0498086a1fa4_a3
      H hDraw
  refine ⟨L, hHL, hLDraw, ?_⟩
  intro M hLM hMDraw
  by_contra hML
  have hstrict :=
    WilliamsonShmoys.pair_count_strict_of_strict_subgraph__p2m_bb57e846_d9a4_493d_944c_0498086a1fa4_a3
      L M hLM hML
  exact (not_lt_of_ge (hmax M (hHL.trans hLM) hMDraw)) hstrict