-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_790c0277_1cda_4997_aaa7_2744ce166f52_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:09:25.630915+00:00
-- url     : https://prove2.me/submissions/0ecfd143-d020-4fcb-b10f-0ad8feb7fbae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_afc05135_ebe6_4750_8043_cdffdef73084_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_afc05135_ebe6_4750_8043_cdffdef73084_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L → H ≤ L → L = H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  have hUpper :=
    WilliamsonShmoys.planar_edge_count_upper_bound__p2m_afc05135_ebe6_4750_8043_cdffdef73084_a1
      H hcard hdraw
  have hLower :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_afc05135_ebe6_4750_8043_cdffdef73084_a1
      H hcard hdraw hmax
  omega