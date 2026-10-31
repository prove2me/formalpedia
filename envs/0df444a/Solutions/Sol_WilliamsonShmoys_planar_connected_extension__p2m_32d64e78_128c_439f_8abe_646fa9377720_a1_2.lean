-- Prove2me | solution 2 for WilliamsonShmoys.planar_connected_extension__p2m_32d64e78_128c_439f_8abe_646fa9377720_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:26:43.226261+00:00
-- url     : https://prove2.me/submissions/df3bd4e5-06a5-455a-9cac-cc20c798d279

import Theorems.Thm_WilliamsonShmoys_exists_connected_planar_supergraph__p2m_c955d1e3_af39_465d_8618_7c677be66dad_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K :=
  WilliamsonShmoys.exists_connected_planar_supergraph__p2m_c955d1e3_af39_465d_8618_7c677be66dad_a1 H hH hV
