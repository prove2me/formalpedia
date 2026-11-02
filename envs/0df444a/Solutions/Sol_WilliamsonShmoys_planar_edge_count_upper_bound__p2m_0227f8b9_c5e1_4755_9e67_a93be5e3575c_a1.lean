-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_0227f8b9_c5e1_4755_9e67_a93be5e3575c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:32:15.01037+00:00
-- url     : https://prove2.me/submissions/c8076264-209a-499a-b9ed-25e4ce7ff0dd

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_09ac247b_fe9e_49f3_a563_2231c8d12f27_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    letI : DecidableRel Q.Adj := Classical.decRel Q.Adj
    Q.edgeFinset.card + 6 <= 3 * Fintype.card V := by
  classical
  have hext :=
    WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_09ac247b_fe9e_49f3_a563_2231c8d12f27_a1
      Q hcard hQ
  cases hext with
  | intro R hrest =>
    cases hrest with
    | intro hsub hrest =>
      cases hrest with
      | intro hRplanar hrest =>
        cases hrest with
        | intro hcard_le hRcount =>
          calc
            Q.edgeFinset.card + 6 <= R.edgeFinset.card + 6 := Nat.add_le_add_right hcard_le 6
            _ = 3 * Fintype.card V := hRcount