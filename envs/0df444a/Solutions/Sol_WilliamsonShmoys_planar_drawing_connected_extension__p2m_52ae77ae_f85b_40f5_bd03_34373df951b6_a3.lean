-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:41:57.049373+00:00
-- url     : https://prove2.me/submissions/02d34065-3400-4ef6-a5f6-8dd5ebd04ddc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_extension_of_local_step__p2m_c8645d84_972c_4350_854f_f6f7bdb58b09_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_component_bridge__p2m_c8645d84_972c_4350_854f_f6f7bdb58b09_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by
  classical
  apply WilliamsonShmoys.planar_connected_extension_of_local_step__p2m_c8645d84_972c_4350_854f_f6f7bdb58b09_a1 K hK
  intro G hKG hG hGdis
  exact WilliamsonShmoys.planar_drawing_component_bridge__p2m_c8645d84_972c_4350_854f_f6f7bdb58b09_a1 G hG hcard hGdis