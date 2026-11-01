-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_exact_edge_count__p2m_258eb918_9051_4673_9031_77873604d1c1_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:51:20.499819+00:00
-- url     : https://prove2.me/submissions/e96f89a1-0943-4c46-8cf3-01b8f598c3c2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_maximal_planar_exact_edge_count__p2m_861504bb_9b69_4346_abcf_17510b6445ad_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_lower_edge_bound__p2m_861504bb_9b69_4346_abcf_17510b6445ad_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     3 * Fintype.card V - 6 = H.edgeFinset.card) := by
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hup := WilliamsonShmoys.planar_edge_bound_for_maximal_planar_exact_edge_count__p2m_861504bb_9b69_4346_abcf_17510b6445ad_a1
    H hcard hH
  have hlo := WilliamsonShmoys.maximal_planar_lower_edge_bound__p2m_861504bb_9b69_4346_abcf_17510b6445ad_a1
    H hcard hH hmax
  omega