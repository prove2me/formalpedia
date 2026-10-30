-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_is_connected__p2m_97829890_428d_4657_a899_f7e200a68a7c_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T01:01:04.396504+00:00
-- url     : https://prove2.me/submissions/f2f8cc6c-c513-44c2-8ca1-08690702947d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_drawing_strict_extension__p2m_8603d9a1_7393_4bbf_851c_41d8426e3226_a2
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    K.Connected := by
  by_contra hconn
  obtain ⟨L, hKL, hneq, hL⟩ :=
    WilliamsonShmoys.disconnected_drawing_strict_extension__p2m_8603d9a1_7393_4bbf_851c_41d8426e3226_a2
      K hK hCard hconn
  exact hneq (hMax L hKL hL)