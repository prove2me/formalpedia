-- Prove2me | solution 2 for WilliamsonShmoys.planar_triangulation_completion__p2m_14be45b2_4af8_4477_b67a_6d2fa4a08c68_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:22:17.485048+00:00
-- url     : https://prove2.me/submissions/4f15e810-d09c-4d1e-9a67-6ef609e9910a

import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_triangulation_extension_db2981d6
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planarDrawingOn_triangulation_extension_db2981d6 K hcard hK
