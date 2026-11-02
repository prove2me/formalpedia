-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_maximalExtension__p2m_bc222e64_5fd0_4544_bad9_127a7d6f7d68_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:19:26.678514+00:00
-- url     : https://prove2.me/submissions/5dd0509e-7eca-406e-9b4c-bbeb9874199b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_predicate__p2m_1e3a6908_3e59_4565_92f0_171f972a39c8_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ K' : SimpleGraph V, K ≤ K' → HasPlanarDrawingOn K' → K' = K := by
  exact WilliamsonShmoys.exists_maximal_supergraph_for_predicate__p2m_1e3a6908_3e59_4565_92f0_171f972a39c8_a2
    (P := HasPlanarDrawingOn) H hH