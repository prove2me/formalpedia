-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_a41fea2b_c624_4d83_8365_0ca98a452bee_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:09:11.481349+00:00
-- url     : https://prove2.me/submissions/82d3abc6-987d-4f31-b7fb-7afcdf60261d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_64c9133b_a623_45e5_bf52_4877372e6864_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_64c9133b_a623_45e5_bf52_4877372e6864_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ Q : SimpleGraph V,
      (∀ {u v : V}, P.Adj u v → Q.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn Q →
      (∀ {u v : V}, Q.Adj u v → P.Adj u v)) :
    letI : DecidableRel P.Adj := Classical.decRel P.Adj
    P.edgeFinset.card = 3 * Fintype.card V - 6 := by
  classical
  have hupper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_64c9133b_a623_45e5_bf52_4877372e6864_a1 P hP hcard
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_64c9133b_a623_45e5_bf52_4877372e6864_a1 P hP hcard hmax
  omega