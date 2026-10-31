-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension_c7059b55_ff77_4f00_a57a_8983712db7a5
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:30:00.018406+00:00
-- url     : https://prove2.me/submissions/4a9b49a4-c3a9-4657-9c32-1463508ed80a

import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_connected_supergraph

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ N.Connected ∧ HasPlanarDrawingOn N :=
  WilliamsonShmoys.planar_drawing_has_connected_supergraph M hM hV
