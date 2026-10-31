-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_09b502cd_aaf2_445b_949d_80cdcc13c52d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:01:43.241863+00:00
-- url     : https://prove2.me/submissions/96102c1e-f348-49a2-8a03-e034f95bbe12

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_9fdf65a3_2cbf_4cec_9951_ee8b977e74bf_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_9fdf65a3_2cbf_4cec_9951_ee8b977e74bf_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) (hV : 3 <= Fintype.card V) (hMax : forall N : SimpleGraph V, Set.Subset M.edgeSet N.edgeSet -> WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) : M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_edge_upper_bound__p2m_9fdf65a3_2cbf_4cec_9951_ee8b977e74bf_a2 M hDraw hV
  have hLower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_9fdf65a3_2cbf_4cec_9951_ee8b977e74bf_a1 M hDraw hV hMax
  omega