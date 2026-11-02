-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_graph__p2m_d6b9112d_6e11_42e8_8b1b_3d46cf1b698c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:59:34.092591+00:00
-- url     : https://prove2.me/submissions/c157988e-4445-451d-851c-281695506adc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_eq__p2m_3ab951ac_7c5a_45ca_9684_f3fed84a5e33_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  have hEq := WilliamsonShmoys.maximal_planar_edge_count_eq__p2m_3ab951ac_7c5a_45ca_9684_f3fed84a5e33_a1
    K hcard hK hmax
  exact le_of_eq hEq.symm