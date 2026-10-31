-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_extension__p2m_931a7134_e35c_41e8_a8b3_e1bad0c19dd8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:04:14.284992+00:00
-- url     : https://prove2.me/submissions/d6001c79-dac6-4b12-8450-7820e3d20c5a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_graph_property_has_maximal_extension__p2m_b14cb1c9_e46e_498d_93f0_e98be9265b47_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ W : SimpleGraph V, G ≤ W ∧ HasPlanarDrawingOn W ∧
      ∀ H : SimpleGraph V, W ≤ H → HasPlanarDrawingOn H → H = W := by
  exact WilliamsonShmoys.finite_graph_property_has_maximal_extension__p2m_b14cb1c9_e46e_498d_93f0_e98be9265b47_a1
    (P := HasPlanarDrawingOn) G hG