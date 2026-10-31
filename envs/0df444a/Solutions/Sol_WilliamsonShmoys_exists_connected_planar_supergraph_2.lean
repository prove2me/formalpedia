-- Prove2me | solution 2 for WilliamsonShmoys.exists_connected_planar_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:43:12.964988+00:00
-- url     : https://prove2.me/submissions/27d93db3-0cbb-4699-b673-4c16b274b9b5

import Theorems.Thm_WilliamsonShmoys_exists_connected_planar_supergraph__p2m_c955d1e3_af39_465d_8618_7c677be66dad_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn K :=
  WilliamsonShmoys.exists_connected_planar_supergraph__p2m_c955d1e3_af39_465d_8618_7c677be66dad_a1 H hH hV
