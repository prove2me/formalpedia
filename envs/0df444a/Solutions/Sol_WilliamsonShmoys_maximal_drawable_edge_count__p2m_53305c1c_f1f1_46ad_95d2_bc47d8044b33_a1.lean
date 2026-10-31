-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count__p2m_53305c1c_f1f1_46ad_95d2_bc47d8044b33_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:53:51.419149+00:00
-- url     : https://prove2.me/submissions/f19b5113-3dc0-41e0-b666-6a5c169371c4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulating_supergraph__p2m_81563a54_65ad_41c2_b8fa_9b4ca4b4c4bf_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ H : SimpleGraph V, L ≤ H → HasPlanarDrawingOn H → H = L)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by
  obtain ⟨H, hLH, hH, hcount⟩ :=
    WilliamsonShmoys.drawable_graph_has_triangulating_supergraph__p2m_81563a54_65ad_41c2_b8fa_9b4ca4b4c4bf_a2
      L hL hV
  have hEq : H = L := hmax H hLH hH
  rw [← hEq]
  exact hcount.symm.le