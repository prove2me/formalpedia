-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_maximal_planar_supergraph__p2m_b8daf038_e3c0_4a60_b7f6_5a7661d4dadb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:57:13.181348+00:00
-- url     : https://prove2.me/submissions/dbe6f000-7704-4eed-9f31-fbd2512f0fda

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_graph_property_maximal_extension__p2m_e07f1b1a_1ea6_4563_8b26_8f130e22d586_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K := by
  classical
  apply WilliamsonShmoys.finite_graph_property_maximal_extension__p2m_e07f1b1a_1ea6_4563_8b26_8f130e22d586_a2
    (P := HasPlanarDrawingOn) (H := H)
    (B := Nat.card (Sym2 V))
  · exact hH
  · intro G hG
    exact Set.ncard_le_card (s := G.edgeSet)