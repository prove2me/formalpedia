-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulating_supergraph__p2m_a35bc758_b19f_4723_ab77_549993b145fc_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:24:14.590359+00:00
-- url     : https://prove2.me/submissions/c8830405-f64a-441b-9def-7e979ad9d4a4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_for_edge_bound_ef555edc

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨H, hKH, hH, hle, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_extension_for_edge_bound_ef555edc K hV hK
  exact ⟨H, hKH, hH, hcount, hle⟩
