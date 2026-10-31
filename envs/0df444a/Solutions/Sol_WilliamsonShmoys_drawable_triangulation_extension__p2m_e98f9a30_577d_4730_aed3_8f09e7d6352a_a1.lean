-- Prove2me | solution 1 for WilliamsonShmoys.drawable_triangulation_extension__p2m_e98f9a30_577d_4730_aed3_8f09e7d6352a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:50:31.736162+00:00
-- url     : https://prove2.me/submissions/b4fb32d2-9786-4052-ba62-5c0242f0986a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_triangulation_maximal_extension__p2m_c8388ff0_77e3_49f1_bb1d_428d2f9c95cd_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_lower_bound__p2m_c8388ff0_77e3_49f1_bb1d_428d2f9c95cd_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧
      3 * (Fintype.card V - 2) ≤ H.edgeSet.ncard := by
  obtain ⟨H, hKH, hH, hmax⟩ :=
    WilliamsonShmoys.drawable_triangulation_maximal_extension__p2m_c8388ff0_77e3_49f1_bb1d_428d2f9c95cd_a1 K hK
  have hbound :=
    WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_c8388ff0_77e3_49f1_bb1d_428d2f9c95cd_a1 H hV hH hmax
  exact ⟨H, hKH, hH, hbound⟩