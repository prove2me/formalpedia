-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_14aa0c9f_f5a1_4cc0_8732_cecb86e5e8ad_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:54:48.223079+00:00
-- url     : https://prove2.me/submissions/9653276a-638e-4cae-a9ac-092945690230

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_lower_edge_bound__p2m_517c01cd_00fc_45c6_9fdb_091b579590d9_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_517c01cd_00fc_45c6_9fdb_091b579590d9_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V)
    (hmax : forall H : SimpleGraph V, K <= H -> WilliamsonShmoys.HasPlanarDrawingOn H -> H <= K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hlow : 3 * Fintype.card V <= K.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_planar_drawing_lower_edge_bound__p2m_517c01cd_00fc_45c6_9fdb_091b579590d9_a1
      K hK hV hmax
  have hupp : K.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
    WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_517c01cd_00fc_45c6_9fdb_091b579590d9_a1
      K hK hV
  omega