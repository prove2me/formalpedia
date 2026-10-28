-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_certificate_of_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:42:47.633931+00:00
-- url     : https://prove2.me/submissions/b61a5bd0-0244-4068-83cd-6233123a3861
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlanarTriangulationCertificate
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_triangulation_extension_edge_count_1bb3a12b_18f2_4a01_afbb_d45898a830ec

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn G) (hconn : G.Connected)
    (hV : 3 <= Fintype.card V) : Nonempty (PlanarTriangulationCertificate G) := by
  obtain ⟨H, hcontains, hedges⟩ :=
    WilliamsonShmoys.planar_drawing_connected_triangulation_extension_edge_count_1bb3a12b_18f2_4a01_afbb_d45898a830ec
      G hdraw hconn hV
  refine ⟨⟨H, hcontains, 2 * Fintype.card V - 4, ?_, ?_⟩⟩ <;> omega
