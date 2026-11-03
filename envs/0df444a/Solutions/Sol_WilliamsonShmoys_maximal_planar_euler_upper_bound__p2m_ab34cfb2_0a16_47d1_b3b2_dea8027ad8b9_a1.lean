-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_euler_upper_bound__p2m_ab34cfb2_0a16_47d1_b3b2_dea8027ad8b9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:05:39.082325+00:00
-- url     : https://prove2.me/submissions/b2037726-612f-480e-9c8d-2a86cf6de91f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_upper_bound_edge_maximal_extension__p2m_c58ab109_98ab_4847_a67d_ff33bea8d7ac_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_upper_bound_maximal_case__p2m_c58ab109_98ab_4847_a67d_ff33bea8d7ac_a1
import Mathlib

set_option autoImplicit false

open scoped BigOperators

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    K.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  classical
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  obtain ⟨H, hKH, hH, hmax, hmono⟩ :=
    WilliamsonShmoys_maximal_planar_euler_upper_bound_edge_maximal_extension__p2m_c58ab109_98ab_4847_a67d_ff33bea8d7ac_a1
      K hK
  have hEuler :=
    WilliamsonShmoys_maximal_planar_euler_upper_bound_maximal_case__p2m_c58ab109_98ab_4847_a67d_ff33bea8d7ac_a1
      H hH hcard hmax
  omega