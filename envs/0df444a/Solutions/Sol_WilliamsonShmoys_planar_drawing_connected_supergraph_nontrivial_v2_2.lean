-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_supergraph_nontrivial_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:48:17.565984+00:00
-- url     : https://prove2.me/submissions/8be24394-c8e0-45c3-b143-9d2ef8c6e14d

import Theorems.Thm_WilliamsonShmoys_exists_connected_planar_supergraph__p2m_c955d1e3_af39_465d_8618_7c677be66dad_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hV : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, W ≤ K ∧ K.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn K :=
  WilliamsonShmoys.exists_connected_planar_supergraph__p2m_c955d1e3_af39_465d_8618_7c677be66dad_a1 W hdraw hV
