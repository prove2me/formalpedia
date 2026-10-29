-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_20afdcd4_5dba_470f_a57a_287711f6e0ce_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T21:13:40.198997+00:00
-- url     : https://prove2.me/submissions/f9baa9ea-c9db-43c2-ae8d-67f59abf4a29
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_c4dc32d3_4855_4c98_90fe_4846f7b25dee_a2
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_lower_bound__p2m_c4dc32d3_4855_4c98_90fe_4846f7b25dee_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N -> M <= N -> N = M)
    (hCard : 3 <= Fintype.card V) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c4dc32d3_4855_4c98_90fe_4846f7b25dee_a2 M hM hCard
  have hLower := WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_c4dc32d3_4855_4c98_90fe_4846f7b25dee_a2 M hM hMax hCard
  omega