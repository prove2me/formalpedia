-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound_20261028
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T03:00:59.604626+00:00
-- url     : https://prove2.me/submissions/036f1913-ace7-47f1-931f-be3ba30080bf

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_extension_20261028
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_upper_bound_20261028

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hsub, hHdraw, hHmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_drawing_extension_20261028 K hK hCard
  have hBound :=
    WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound_20261028
      H hHdraw hHmax hCard
  have hEdges : K.edgeSet.ncard ≤ H.edgeSet.ncard :=
    Set.ncard_le_ncard hsub
  exact (Nat.add_le_add_right hEdges 6).trans hBound
