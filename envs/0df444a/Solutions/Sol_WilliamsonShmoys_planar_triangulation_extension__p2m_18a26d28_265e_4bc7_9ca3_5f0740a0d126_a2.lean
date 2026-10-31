-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_18a26d28_265e_4bc7_9ca3_5f0740a0d126_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:19:46.005593+00:00
-- url     : https://prove2.me/submissions/46ebfa44-ac82-4232-86a1-6232122be091

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_444bbc12_374a_443e_a15d_6bd6256fef03_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_444bbc12_374a_443e_a15d_6bd6256fef03_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hconn : X.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ Y : SimpleGraph V,
      X ≤ Y ∧ WilliamsonShmoys.HasPlanarDrawingOn Y ∧
        Y.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨Y, hXY, hYplanar, hYmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension__p2m_444bbc12_374a_443e_a15d_6bd6256fef03_a1
      X hX hV
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_444bbc12_374a_443e_a15d_6bd6256fef03_a1
      Y hYplanar hV hYmax
  exact ⟨Y, hXY, hYplanar, hcount⟩