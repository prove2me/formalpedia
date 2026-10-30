-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_completion__p2m_715939c0_b6e9_4c03_a6f3_4355f1ffabc5_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T19:20:23.376016+00:00
-- url     : https://prove2.me/submissions/26c77c47-32b8-422f-94e9-d989d89b016f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_0fdafab4_3fd6_4759_8b58_e983a7df1ef3_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_0fdafab4_3fd6_4759_8b58_e983a7df1ef3_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_0fdafab4_3fd6_4759_8b58_e983a7df1ef3_a1
      K hK
  refine ⟨L, hKL, hL, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_0fdafab4_3fd6_4759_8b58_e983a7df1ef3_a1
    L hL hV hmax