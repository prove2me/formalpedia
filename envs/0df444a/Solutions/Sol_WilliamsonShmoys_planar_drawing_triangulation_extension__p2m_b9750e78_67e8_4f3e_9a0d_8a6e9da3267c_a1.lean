-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_b9750e78_67e8_4f3e_9a0d_8a6e9da3267c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:52:10.631924+00:00
-- url     : https://prove2.me/submissions/a737ed6b-b6de-4e6c-842d-398cdbafffbd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_drawable_supergraph__p2m_cb71297e_2af2_47af_8fd1_d009bcc4ef4e_a2
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_cb71297e_2af2_47af_8fd1_d009bcc4ef4e_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard = 3 * (Fintype.card V - 2) := by
  obtain ⟨H, hKH, hH, hcard, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_drawable_supergraph__p2m_cb71297e_2af2_47af_8fd1_d009bcc4ef4e_a2
      K hK
  refine ⟨H, hKH, hH, hcard, ?_⟩
  exact WilliamsonShmoys.maximal_drawable_edge_count__p2m_cb71297e_2af2_47af_8fd1_d009bcc4ef4e_a2
    H hV hH hmax