-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_03e1b202_06dc_4da5_bd81_d67a28c40fa1_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:51:36.74898+00:00
-- url     : https://prove2.me/submissions/ce678339-663b-4042-bdd9-ad794dded841
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_completion__p2m_293782c6_00d7_4355_8c95_0afa44404fcb_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_face_accounting__p2m_293782c6_00d7_4355_8c95_0afa44404fcb_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hsub, hcount, hH, hconn⟩ :=
    WilliamsonShmoys.planar_connected_completion__p2m_293782c6_00d7_4355_8c95_0afa44404fcb_a1
      G hV hG
  obtain ⟨f, heuler, hfaces⟩ :=
    WilliamsonShmoys.connected_planar_face_accounting__p2m_293782c6_00d7_4355_8c95_0afa44404fcb_a1
      H hH hconn hV
  omega