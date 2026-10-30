-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_triangulation_completion__p2m_46c214d7_d1a4_4ee3_932f_e6097b55f369_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:00:11.041175+00:00
-- url     : https://prove2.me/submissions/89cc16b9-995f-4c0c-9271-f76bf1afcc3e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_extension__p2m_0fb24e84_44a0_421e_a186_c4879c0fa6ba_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_0fb24e84_44a0_421e_a186_c4879c0fa6ba_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_drawing_extension__p2m_0fb24e84_44a0_421e_a186_c4879c0fa6ba_a1 K hDraw
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_0fb24e84_44a0_421e_a186_c4879c0fa6ba_a1 L hV hL hmax⟩