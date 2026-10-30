-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_extension__p2m_0e3a5bf5_c35e_4938_9aa7_a032ab0de182_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:31:36.913293+00:00
-- url     : https://prove2.me/submissions/4b0a15c5-d014-45fe-bb72-bbe7ff5e1fc0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_subgraph_closed_maximal__p2m_39578764_0198_4707_9e11_eef0219b5111_a1
import Theorems.Thm_WilliamsonShmoys_drawable_subgraph__p2m_39578764_0198_4707_9e11_eef0219b5111_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L := by
  apply WilliamsonShmoys.finite_subgraph_closed_maximal__p2m_39578764_0198_4707_9e11_eef0219b5111_a1
    (P := WilliamsonShmoys.HasPlanarDrawingOn) (K := K)
  · intro G H hGH hH
    exact WilliamsonShmoys.drawable_subgraph__p2m_39578764_0198_4707_9e11_eef0219b5111_a1 hGH hH
  · exact hDraw