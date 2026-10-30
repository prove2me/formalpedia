-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_09a7ea27_8f3a_49eb_bec8_9d191564106c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:44:15.267335+00:00
-- url     : https://prove2.me/submissions/1217a68a-036d-4001-a143-8f6af7e9f955
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_4cc4094d_71c5_4a34_a593_dbe980be82f8_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_4cc4094d_71c5_4a34_a593_dbe980be82f8_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 = K.edgeSet.ncard := by
  obtain ⟨K, hJK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_4cc4094d_71c5_4a34_a593_dbe980be82f8_a1
      J hJ
  exact ⟨K, hJK, hK,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_4cc4094d_71c5_4a34_a593_dbe980be82f8_a1
      K hK hV hmax⟩