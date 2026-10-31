-- Prove2me | solution 1 for WilliamsonShmoys.drawable_connected_edgeFinset_card_le_three_mul_card_sub_six__p2m_270023aa_f627_4b53_97e3_8e37f4bb2eb9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:45:58.702841+00:00
-- url     : https://prove2.me/submissions/e8b3d6de-898b-4057-ac31-87e2748f1a9e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count__p2m_849752b4_78ce_4d07_98c6_f3ea971ec2cd_a2
import Theorems.Thm_WilliamsonShmoys_planar_face_count_arithmetic__p2m_849752b4_78ce_4d07_98c6_f3ea971ec2cd_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    M.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.planar_drawing_face_count__p2m_849752b4_78ce_4d07_98c6_f3ea971ec2cd_a2
      M hM hconn hcard
  exact WilliamsonShmoys.planar_face_count_arithmetic__p2m_849752b4_78ce_4d07_98c6_f3ea971ec2cd_a2
    (Fintype.card V) M.edgeFinset.card f hcard hEuler hFaces