-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:11:19.882575+00:00
-- url     : https://prove2.me/submissions/15db5839-97dc-458d-8867-d6dabb6ce653

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f_maximal_extension
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f_triangulation_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ T : SimpleGraph V,
      K ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
        T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨T, hKT, hT, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f_maximal_extension
      K hK
  exact ⟨T, hKT, hT,
    WilliamsonShmoys.planar_supergraph_with_euler_count_2ef74a34_fa40_4031_b5f2_5c9a50dcf66f_triangulation_count
      T hV hT hmax⟩
