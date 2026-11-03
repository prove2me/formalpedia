-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_induce__p2m_8fb060ce_122c_4344_a570_6fdb0412375d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:47:36.043072+00:00
-- url     : https://prove2.me/submissions/10e9ba49-38f6-469c-b569-4fc6e46c5b20

import Theorems.Thm_WilliamsonShmoys_planar_drawing_induce__p2m_8fb060ce_122c_4344_a570_6fdb0412375d_a2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) (s : Set V) :
    letI : Fintype {v // v ∈ s} := Fintype.ofFinite _
    HasPlanarDrawingOn (N.induce s) :=
  WilliamsonShmoys.planar_drawing_induce__p2m_8fb060ce_122c_4344_a570_6fdb0412375d_a2 N hN s