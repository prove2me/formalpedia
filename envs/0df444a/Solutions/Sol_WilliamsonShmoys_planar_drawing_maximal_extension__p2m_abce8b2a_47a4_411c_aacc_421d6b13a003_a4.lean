-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_abce8b2a_47a4_411c_aacc_421d6b13a003_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:29:16.600567+00:00
-- url     : https://prove2.me/submissions/ea71bd14-fdad-4c34-8167-ed9dadf267d3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_graph_extension__p2m_0be9f664_4886_4746_8cb3_c25ee67fb6aa_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M) :
    ∃ K : SimpleGraph V, M ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by
  exact WilliamsonShmoys.finite_maximal_graph_extension__p2m_0be9f664_4886_4746_8cb3_c25ee67fb6aa_a1
    M HasPlanarDrawingOn hM