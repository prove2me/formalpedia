-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_data__p2m_b0556792_8fbb_42b1_83f9_e49450aba15a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:18:41.829242+00:00
-- url     : https://prove2.me/submissions/6c06f8ae-b4f1-40a3-ab90-e58c6b3e1d1f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_bounded_extension__p2m_c4d77529_9abd_4bdb_a9e4_27423a3195e5_a3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     Exists fun K : SimpleGraph V => H <= K /\
       (letI : DecidableRel K.Adj := Classical.decRel K.Adj
        H.edgeFinset.card <= K.edgeFinset.card /\
        Exists fun f : Nat => Exists fun l : Nat =>
          Fintype.card V + f = K.edgeFinset.card + 2 /\
          l = 2 * K.edgeFinset.card /\
          3 * f <= l)) := by
  classical
  obtain ⟨K, hHK, hK, hmono, hnle, heub⟩ :=
    WilliamsonShmoys.planar_drawing_bounded_extension__p2m_c4d77529_9abd_4bdb_a9e4_27423a3195e5_a3
      H hcard hH
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  let n : Nat := Fintype.card V
  let e : Nat := K.edgeFinset.card
  have hEq : n + (e + 2 - n) = e + 2 := by
    dsimp [n, e]
    omega
  have hBound : 3 * (e + 2 - n) <= 2 * e := by
    dsimp [n, e]
    omega
  exact ⟨K, hHK, hmono, e + 2 - n, 2 * e, hEq, rfl, hBound⟩