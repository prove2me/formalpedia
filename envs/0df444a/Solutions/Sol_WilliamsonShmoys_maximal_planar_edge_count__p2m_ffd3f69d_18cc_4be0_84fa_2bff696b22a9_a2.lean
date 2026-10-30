-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_ffd3f69d_18cc_4be0_84fa_2bff696b22a9_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:49:51.627733+00:00
-- url     : https://prove2.me/submissions/4e6eaea9-5954-4bef-bc32-31e855f4f52f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_e4274472_fa7f_45c2_bc46_56de2add020a_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_e4274472_fa7f_45c2_bc46_56de2add020a_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
      H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hupper := WilliamsonShmoys.planar_edge_upper_bound__p2m_e4274472_fa7f_45c2_bc46_56de2add020a_a1
    H hH hcard
  have hlower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_e4274472_fa7f_45c2_bc46_56de2add020a_a1
    H hH hmax hcard
  omega