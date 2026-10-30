-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_99cd9976_4307_421c_aac6_f259ef43e42f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:35:42.996449+00:00
-- url     : https://prove2.me/submissions/eaeb29d9-05bf-494e-a8b5-68b897f74150

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_upper_bound__p2m_53911c92_d38e_4043_bb6e_65b3932704cd_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_53911c92_d38e_4043_bb6e_65b3932704cd_a1

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 <= Fintype.card V)
    (hmax : forall K : SimpleGraph V, M <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hlo := WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_53911c92_d38e_4043_bb6e_65b3932704cd_a1 M hM hV hmax
  have hup := WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound__p2m_53911c92_d38e_4043_bb6e_65b3932704cd_a1 M hM hV
  omega