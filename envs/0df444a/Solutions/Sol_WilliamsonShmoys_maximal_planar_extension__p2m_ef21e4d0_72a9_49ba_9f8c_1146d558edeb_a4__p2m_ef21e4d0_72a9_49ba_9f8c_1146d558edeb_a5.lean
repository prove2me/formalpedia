-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension__p2m_ef21e4d0_72a9_49ba_9f8c_1146d558edeb_a4__p2m_ef21e4d0_72a9_49ba_9f8c_1146d558edeb_a5
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:47:52.341872+00:00
-- url     : https://prove2.me/submissions/ec28eeb7-7e82-46ba-aa75-895e01ffb121

import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_ef21e4d0_72a9_49ba_9f8c_1146d558edeb_a7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hCard : 3 <= Fintype.card V)
    (hT : HasPlanarDrawingOn T) :
    exists U : SimpleGraph V,
      (forall x y, T.Adj x y -> U.Adj x y) /\
      HasPlanarDrawingOn U /\
      U.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_extension__p2m_ef21e4d0_72a9_49ba_9f8c_1146d558edeb_a7 T hCard hT
