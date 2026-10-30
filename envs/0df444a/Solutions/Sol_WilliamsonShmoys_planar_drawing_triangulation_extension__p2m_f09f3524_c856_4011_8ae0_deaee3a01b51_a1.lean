-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_f09f3524_c856_4011_8ae0_deaee3a01b51_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:15:55.720146+00:00
-- url     : https://prove2.me/submissions/ff144705-6976-4a07-837c-00cc5641d8e7

import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_99cd9976_4307_421c_aac6_f259ef43e42f_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_99cd9976_4307_421c_aac6_f259ef43e42f_a1

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hV : 3 <= Fintype.card V) :
    exists M : SimpleGraph V,
      N <= M /\ WilliamsonShmoys.HasPlanarDrawingOn M /\
        M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  cases WilliamsonShmoys.planar_drawing_maximal_extension__p2m_99cd9976_4307_421c_aac6_f259ef43e42f_a1 N hN with
  | intro M hM0 =>
    cases hM0 with
    | intro hNM hM1 =>
      cases hM1 with
      | intro hM hmax =>
        exact Exists.intro M (And.intro hNM (And.intro hM
          (WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_99cd9976_4307_421c_aac6_f259ef43e42f_a1 M hM hV hmax)))