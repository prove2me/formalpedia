-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planarDrawingOn_edge_count_fe74ac1b_216e_4ca8_b058_0b3c4a531007
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:17:39.890291+00:00
-- url     : https://prove2.me/submissions/821dcf4d-bf58-492a-bd0e-bd2cfec293e5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_d50d73e2_914c_4c79_8582_24c0dc335bdf_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_d50d73e2_914c_4c79_8582_24c0dc335bdf_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_d50d73e2_914c_4c79_8582_24c0dc335bdf_a1
    K hDraw hCard
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_d50d73e2_914c_4c79_8582_24c0dc335bdf_a1
    K hDraw hCard hMax
  omega