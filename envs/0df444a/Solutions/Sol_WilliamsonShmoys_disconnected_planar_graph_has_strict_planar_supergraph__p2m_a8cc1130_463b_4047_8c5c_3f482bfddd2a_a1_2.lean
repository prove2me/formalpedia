-- Prove2me | solution 2 for WilliamsonShmoys.disconnected_planar_graph_has_strict_planar_supergraph__p2m_a8cc1130_463b_4047_8c5c_3f482bfddd2a_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:24:13.205897+00:00
-- url     : https://prove2.me/submissions/7902e9ed-1b3c-48f4-8242-e32ada4edbb4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hNotConnected : ¬ H.Connected) :
    ∃ M : SimpleGraph V,
      H ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M ≠ H := by
  obtain ⟨J, hHJ, hne, hJ⟩ :=
    WilliamsonShmoys.planar_edge_extension_of_disconnected_drawing H hH hV hNotConnected
  exact ⟨J, hHJ, hJ, hne⟩
