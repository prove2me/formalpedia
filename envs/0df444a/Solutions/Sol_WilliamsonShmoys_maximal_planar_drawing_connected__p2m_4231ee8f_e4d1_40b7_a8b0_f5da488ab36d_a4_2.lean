-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_connected__p2m_4231ee8f_e4d1_40b7_a8b0_f5da488ab36d_a4
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:28:54.51377+00:00
-- url     : https://prove2.me/submissions/c7498884-b86e-4c29-b5e8-dbd3c052a77e

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_connected_from_maximality_afa305d5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, H ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = H) :
    H.Connected :=
  WilliamsonShmoys.maximal_planar_drawing_connected_from_maximality_afa305d5 H hH hV hMax
