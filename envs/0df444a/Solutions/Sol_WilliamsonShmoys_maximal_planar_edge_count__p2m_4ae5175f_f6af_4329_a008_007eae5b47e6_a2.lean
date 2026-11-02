-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_4ae5175f_f6af_4329_a008_007eae5b47e6_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:15:29.544756+00:00
-- url     : https://prove2.me/submissions/a8bc0608-e144-4561-a6b8-c8513e4bc411
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_535e4e7e_28ad_48ed_9188_305d88c71848_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_535e4e7e_28ad_48ed_9188_305d88c71848_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    L.edgeFinset.card + 6 = 3 * Fintype.card V := by
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  have hupper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_535e4e7e_28ad_48ed_9188_305d88c71848_a1 L hV hL
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_535e4e7e_28ad_48ed_9188_305d88c71848_a1 L hV hL hmax
  omega