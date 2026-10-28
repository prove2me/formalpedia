-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_count_upper__p2m_a57dc3db_20ea_40d3_9b0f_dcd4c88e6cc2_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:58:44.612629+00:00
-- url     : https://prove2.me/submissions/2629fd1e-349b-4c77-869d-2924b374a1b6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_face_accounting_57972424
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_e750187a_6814_42ad_9805_f7d2cd135631_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V) :
    L.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hEdges, hConnected, hDrawing⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension__p2m_e750187a_6814_42ad_9805_f7d2cd135631_a2
      L hDraw hCard
  have hH :=
    WilliamsonShmoys.planar_edge_bound_for_face_accounting_57972424
      H hDrawing hConnected hCard
  omega