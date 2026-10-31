-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_49092f42_4606_480d_84ab_7522b76f4e32_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:06:26.181372+00:00
-- url     : https://prove2.me/submissions/d1ace1d9-a884-4199-a7b6-48c7b6fb6a53

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_18a26d28_265e_4bc7_9ca3_5f0740a0d126_a2
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono__p2m_18a26d28_265e_4bc7_9ca3_5f0740a0d126_a2
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (X : SimpleGraph V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X) (hconn : X.Connected)
    (hV : 3 ≤ Fintype.card V) : X.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨Y, hXY, hY, htri⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_18a26d28_265e_4bc7_9ca3_5f0740a0d126_a2
      X hX hconn hV
  have hmono : X.edgeSet.ncard ≤ Y.edgeSet.ncard :=
    WilliamsonShmoys.edgeSet_ncard_mono__p2m_18a26d28_265e_4bc7_9ca3_5f0740a0d126_a2
      X Y hXY
  omega