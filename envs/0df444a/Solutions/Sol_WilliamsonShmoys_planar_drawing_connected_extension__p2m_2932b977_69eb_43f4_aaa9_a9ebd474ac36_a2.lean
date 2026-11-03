-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_2932b977_69eb_43f4_aaa9_a9ebd474ac36_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T12:00:05.782291+00:00
-- url     : https://prove2.me/submissions/592a5b2d-2766-4d87-b5de-41f9f0acdadf

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph__p2m_81eecf30_e96c_499d_b4eb_13964c396f7c_a2

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ L.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn L := by
  exact WilliamsonShmoys.planar_connected_supergraph__p2m_81eecf30_e96c_499d_b4eb_13964c396f7c_a2 K hK hcard
