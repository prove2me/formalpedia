-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_connected__p2m_dd78c457_06f8_4973_886c_d0aede564096_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:54:36.534343+00:00
-- url     : https://prove2.me/submissions/aecc91a5-902c-4138-9fad-7db4adddde18

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_connected_from_maximality_afa305d5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.Connected :=
  WilliamsonShmoys.maximal_planar_drawing_connected_from_maximality_afa305d5 H hplanar hV hmax
