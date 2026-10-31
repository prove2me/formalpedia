-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_9d48574e_becf_4744_b845_090de246cf6f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:33:29.979835+00:00
-- url     : https://prove2.me/submissions/ce194d36-ed6d-4066-97c6-372d6802e2f6

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_extension_edge_count

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hDraw : HasPlanarDrawingOn Q) (hV : 3 ≤ Fintype.card V) : ∃ R : SimpleGraph V, Q ≤ R ∧ HasPlanarDrawingOn R ∧ R.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulated_extension_edge_count Q hDraw hV
