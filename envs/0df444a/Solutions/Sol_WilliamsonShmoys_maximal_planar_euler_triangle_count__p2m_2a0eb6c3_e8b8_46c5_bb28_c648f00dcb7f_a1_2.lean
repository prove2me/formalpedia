-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_euler_triangle_count__p2m_2a0eb6c3_e8b8_46c5_bb28_c648f00dcb7f_a1
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:06:24.020571+00:00
-- url     : https://prove2.me/submissions/56c3f2e8-9910-4774-8d6f-59eda6d89014

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition_edge_bound_9a40956c04dd448b9ab680f8d2edf7ce
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_certificate__p2m_42928b97_f6a9_47a4_921a_031377856976_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_0d90a4e2_211c_41d9_a3e6_1089ea8087c9_a1
import Theorems.Thm_WilliamsonShmoys_planar_euler_edge_bound__p2m_a3e0b5a8_b607_4050_8296_f0effeafa525_a2
import Theorems.Thm_WilliamsonShmoys_planar_euler_edge_bound__p2m_a3e0b5a8_b607_4050_8296_f0effeafa525_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition_for_edge_count
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_equations__p2m_27a5cf8c_cedc_4abf_b82c_50a7768c797c_a2
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_671e5c30_1b1f_403c_8a8b_f487cd0d141b_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_e696380b
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_euler_edge_count

set_option autoImplicit false
open WilliamsonShmoys
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H ≤ K) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by
  exact maximal_planar_face_count_certificate__p2m_42928b97_f6a9_47a4_921a_031377856976_a1 K hV hK hmax
