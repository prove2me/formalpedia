-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_60570168_fc59_4828_82d8_84f6b859c6a0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:00:27.551223+00:00
-- url     : https://prove2.me/submissions/a33c7638-5f76-46fd-ae4b-52dcad4ce497
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_d133570c_99c6_41e5_a60e_ff6fc0c72c59_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_d133570c_99c6_41e5_a60e_ff6fc0c72c59_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, K ≤ M → HasPlanarDrawingOn M → M ≤ K) :
    (letI : DecidableRel K.Adj := dK;
      K.edgeFinset.card = 3 * Fintype.card V - 6) := by
  letI : DecidableRel K.Adj := dK
  have hu := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_d133570c_99c6_41e5_a60e_ff6fc0c72c59_a1
    K dK hK hcard
  have hl := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_d133570c_99c6_41e5_a60e_ff6fc0c72c59_a1
    K dK hK hcard hmax
  omega