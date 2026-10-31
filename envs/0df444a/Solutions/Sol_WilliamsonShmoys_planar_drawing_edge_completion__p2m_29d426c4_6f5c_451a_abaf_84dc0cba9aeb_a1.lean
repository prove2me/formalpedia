-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_completion__p2m_29d426c4_6f5c_451a_abaf_84dc0cba9aeb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:34:36.473095+00:00
-- url     : https://prove2.me/submissions/3d2bb8b0-2dfa-4e8c-b809-ef26ff0f0200

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_maximal_completion__p2m_09f5e978_2c83_4c51_aef8_e686b5a5e02c_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_09f5e978_2c83_4c51_aef8_e686b5a5e02c_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) :
    ∃ J : SimpleGraph V, H ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J ∧
      3 * Fintype.card V - 6 = J.edgeSet.ncard := by
  obtain ⟨J, hHJ, hJ, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_edge_maximal_completion__p2m_09f5e978_2c83_4c51_aef8_e686b5a5e02c_a1 H hH
  exact ⟨J, hHJ, hJ,
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_09f5e978_2c83_4c51_aef8_e686b5a5e02c_a1 J hJ hV hmax⟩