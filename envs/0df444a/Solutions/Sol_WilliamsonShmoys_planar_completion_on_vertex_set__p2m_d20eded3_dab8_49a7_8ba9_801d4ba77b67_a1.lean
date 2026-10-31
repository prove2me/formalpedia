-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_on_vertex_set__p2m_d20eded3_dab8_49a7_8ba9_801d4ba77b67_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:58:03.089391+00:00
-- url     : https://prove2.me/submissions/be2b8533-9b32-4e19-9b4d-d00c031c8fad
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_a5f3545b_9213_4099_bf3a_a8a2e64023e0_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_a5f3545b_9213_4099_bf3a_a8a2e64023e0_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : LE.le 3 (Fintype.card V))
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ T' : SimpleGraph V,
      LE.le T T' ∧ WilliamsonShmoys.HasPlanarDrawingOn T' ∧
      T'.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨T', hsub, hplanar, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a5f3545b_9213_4099_bf3a_a8a2e64023e0_a1
      T hV hT
  exact ⟨T', hsub, hplanar,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_a5f3545b_9213_4099_bf3a_a8a2e64023e0_a1
      T' hV hplanar hmax⟩