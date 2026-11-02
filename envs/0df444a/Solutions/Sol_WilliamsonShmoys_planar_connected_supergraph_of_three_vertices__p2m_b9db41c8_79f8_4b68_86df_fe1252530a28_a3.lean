-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_supergraph_of_three_vertices__p2m_b9db41c8_79f8_4b68_86df_fe1252530a28_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T23:31:16.65892+00:00
-- url     : https://prove2.me/submissions/3cd08f9d-ae81-4fcc-a9e0-e1e72a0046a3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_exists

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K := by
  exact WilliamsonShmoys.planar_drawing_connected_extension_exists H hcard hH
