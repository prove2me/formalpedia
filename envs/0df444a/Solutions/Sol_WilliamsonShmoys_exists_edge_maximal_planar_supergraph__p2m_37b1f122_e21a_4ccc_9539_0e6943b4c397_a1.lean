-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_37b1f122_e21a_4ccc_9539_0e6943b4c397_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:32:42.078955+00:00
-- url     : https://prove2.me/submissions/9bd92086-9a69-46e4-8d98-9080fdbeec4b

import Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_of_finite_predicate__p2m_65144f9b_062d_49b2_8349_18e0af58320c_a1
import Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_of_le__p2m_65144f9b_062d_49b2_8349_18e0af58320c_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L) :
    ∃ T : SimpleGraph V,
      L ≤ T ∧ HasPlanarDrawingOn T ∧
        ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U ≤ T := by
  obtain ⟨T, hLT, hT, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_extension_of_finite_predicate__p2m_65144f9b_062d_49b2_8349_18e0af58320c_a1
      L HasPlanarDrawingOn hL
      (by
        intro G H hGH hH
        exact WilliamsonShmoys.hasPlanarDrawingOn_of_le__p2m_65144f9b_062d_49b2_8349_18e0af58320c_a1 hGH hH)
  exact ⟨T, hLT, hT, hmax⟩