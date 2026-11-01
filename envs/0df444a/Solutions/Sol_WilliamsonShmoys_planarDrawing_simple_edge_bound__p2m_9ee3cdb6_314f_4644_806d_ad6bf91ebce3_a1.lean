-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_simple_edge_bound__p2m_9ee3cdb6_314f_4644_806d_ad6bf91ebce3_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:46:28.53959+00:00
-- url     : https://prove2.me/submissions/3342e7eb-107a-40f3-88d8-58fe32044f6c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planarDrawing_euler_face_certificate__p2m_68659add_1ba6_4067_be65_c7b40be0a2e9_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hConn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 6 ≤
      3 * Fintype.card V := by
  letI : DecidableRel G.Adj := dG
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.planarDrawing_euler_face_certificate__p2m_68659add_1ba6_4067_be65_c7b40be0a2e9_a1
      G dG hG hConn hcard
  omega