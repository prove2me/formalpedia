-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_15067ae2_6164_4683_8340_3852ef322251_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:17:11.259671+00:00
-- url     : https://prove2.me/submissions/5df9d84f-dede-4fa7-ab42-ae052923a293

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_b4696467_bd7a_4833_91a4_199ab5144504_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_b4696467_bd7a_4833_91a4_199ab5144504_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L → K ≤ L → K = L)
    (hcard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper :=
    WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_b4696467_bd7a_4833_91a4_199ab5144504_a1
      K hplanar hcard
  have hlower :=
    WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_b4696467_bd7a_4833_91a4_199ab5144504_a1
      K hplanar hmax hcard
  omega