-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_completion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:10:49.267525+00:00
-- url     : https://prove2.me/submissions/e4c3d18b-a1db-4f18-b7a7-7c853e33c021
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_same_vertex_edge_maximal_planar_supergraph
import Theorems.Thm_WilliamsonShmoys_same_vertex_edge_maximal_planar_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    ∃ G : SimpleGraph V,
      H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G ∧
        G.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨G, hHG, hGplanar, hGmax⟩ :=
    WilliamsonShmoys.exists_same_vertex_edge_maximal_planar_supergraph H hV hH hconn
  have hcount :=
    WilliamsonShmoys.same_vertex_edge_maximal_planar_edge_count G hV hGplanar hGmax
  exact ⟨G, hHG, hGplanar, hcount⟩