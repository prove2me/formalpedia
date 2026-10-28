-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound_v3_triangulation_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:20:56.309532+00:00
-- url     : https://prove2.me/submissions/5a2f24eb-e313-4ea6-8d2f-21454d81c1c8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_v3_triangulation_extension_maximal_extension
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_v3_triangulation_extension_maximal_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hConn : H.Connected) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard := by
  obtain ⟨K, hHK, hKDraw, hKMax, hCardLE⟩ :=
    WilliamsonShmoys.connected_planar_edge_bound_v3_triangulation_extension_maximal_extension
      H hV hDraw hConn
  have hCount :=
    WilliamsonShmoys.connected_planar_edge_bound_v3_triangulation_extension_maximal_edge_count
      K hV hKDraw hKMax
  exact ⟨K, hHK, hKDraw, hCount, hCardLE⟩