-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_88a3bf29_1582_4605_aca9_2743ecb4531b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:33:31.689984+00:00
-- url     : https://prove2.me/submissions/b49772ff-94de-4f2d-8357-f99e9e902305
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_supergraph__p2m_21c51033_6ced_4e68_8653_efea3430d001_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) : G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hsub, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulated_supergraph__p2m_21c51033_6ced_4e68_8653_efea3430d001_a1
      G hDraw hV
  calc
    G.edgeSet.ncard ≤ H.edgeSet.ncard := Set.ncard_mono hsub
    _ = 3 * Fintype.card V - 6 := hcard