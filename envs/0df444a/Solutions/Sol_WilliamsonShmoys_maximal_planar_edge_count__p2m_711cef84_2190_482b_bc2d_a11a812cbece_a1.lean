-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_711cef84_2190_482b_bc2d_a11a812cbece_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:00:31.632364+00:00
-- url     : https://prove2.me/submissions/36d1e9bb-aae8-4314-a40b-60f1ea7e55c6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_upper_bound__p2m_e972185b_4990_47b3_b33a_686d33f273ec_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_e972185b_4990_47b3_b33a_686d33f273ec_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, HasPlanarDrawingOn K →
      (∀ u v, H.Adj u v → K.Adj u v) →
      ∀ u v, K.Adj u v → H.Adj u v) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
      H.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hup := WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_e972185b_4990_47b3_b33a_686d33f273ec_a1 H hV hH
  have hlo := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_e972185b_4990_47b3_b33a_686d33f273ec_a1 H hV hH hmax
  exact Nat.le_antisymm hup hlo