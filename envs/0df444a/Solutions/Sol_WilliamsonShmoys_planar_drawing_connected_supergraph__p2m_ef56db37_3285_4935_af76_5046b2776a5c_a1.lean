-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_ef56db37_3285_4935_af76_5046b2776a5c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T23:15:50.63574+00:00
-- url     : https://prove2.me/submissions/4d081a93-58cf-4357-944a-4b848d2a7bc0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_exists

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ L.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn L := by
  exact WilliamsonShmoys.planar_drawing_connected_extension_exists K hcard hK
