-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_b5935805_1780_4fdc_8b62_9214cd276435_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T23:42:42.367427+00:00
-- url     : https://prove2.me/submissions/f5b40fde-8d06-4c11-8863-a576416d93ba

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_c00979a8_planar_edge_bound
import Theorems.Thm_WilliamsonShmoys_edgeFinset_card_le_edgeSet_ncard_of_subset__p2m_a34ee183_b91b_4a67_873f_251f94ba9522_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj;
      G.edgeFinset.card + 6 <= 3 * Fintype.card V) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hrepr : G.edgeFinset.card <= G.edgeSet.ncard :=
    WilliamsonShmoys.edgeFinset_card_le_edgeSet_ncard_of_subset__p2m_a34ee183_b91b_4a67_873f_251f94ba9522_a2
      G G Set.Subset.rfl
  have hbound : G.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_c00979a8_planar_edge_bound
      G hcard hG
  omega
