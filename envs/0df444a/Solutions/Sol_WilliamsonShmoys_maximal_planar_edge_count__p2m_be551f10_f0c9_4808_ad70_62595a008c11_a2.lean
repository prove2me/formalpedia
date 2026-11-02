-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_be551f10_f0c9_4808_ad70_62595a008c11_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:43:36.812019+00:00
-- url     : https://prove2.me/submissions/aaa281ce-f56a-4345-86ed-a13558f29583
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_connected__p2m_b2f31750_6395_4f01_b4dd_f5215a908d6d_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_common_face_count__p2m_b2f31750_6395_4f01_b4dd_f5215a908d6d_a2
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ P : SimpleGraph V, N ≤ P →
      WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    letI : DecidableRel N.Adj := Classical.decRel N.Adj
    N.edgeFinset.card + 6 = 3 * Fintype.card V := by
  classical
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  have hconn :=
    WilliamsonShmoys.maximal_planar_connected__p2m_b2f31750_6395_4f01_b4dd_f5215a908d6d_a1
      N hN hcard hmax
  obtain ⟨f, hEuler, hTri⟩ :=
    WilliamsonShmoys.maximal_planar_common_face_count__p2m_b2f31750_6395_4f01_b4dd_f5215a908d6d_a2
      N hN hconn hcard hmax
  change N.edgeFinset.card + 6 = 3 * Fintype.card V
  omega
