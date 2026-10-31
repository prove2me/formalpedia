-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_upper__p2m_19c9eeac_1bda_4675_8c1b_5590acff2ab1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:26:56.401018+00:00
-- url     : https://prove2.me/submissions/adc7da1d-2f41-4554-9c74-441e77a5a15e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_euler_data__p2m_49196ac4_b46c_446f_b424_262126b1b13c_a2
import Theorems.Thm_WilliamsonShmoys_edge_bound_from_euler_data__p2m_49196ac4_b46c_446f_b424_262126b1b13c_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V) (hDraw : HasPlanarDrawingOn R)
    (hV : 3 <= Fintype.card V) :
    R.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨m', f, hSub, hEuler, hFaces⟩ :=
    WilliamsonShmoys.planar_completion_euler_data__p2m_49196ac4_b46c_446f_b424_262126b1b13c_a2
      R hDraw hV
  exact Nat.le_trans hSub
    (WilliamsonShmoys.edge_bound_from_euler_data__p2m_49196ac4_b46c_446f_b424_262126b1b13c_a2
      (Fintype.card V) m' f hV hEuler hFaces)