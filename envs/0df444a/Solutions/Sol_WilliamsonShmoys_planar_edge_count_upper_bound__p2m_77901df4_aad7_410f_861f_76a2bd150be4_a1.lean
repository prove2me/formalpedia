-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_77901df4_aad7_410f_861f_76a2bd150be4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T23:08:07.233479+00:00
-- url     : https://prove2.me/submissions/2a356cbf-2ef5-4f72-8282-8f148a37a636

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_938af664_b2aa_4ceb_8ad4_a78c6b3943d3
import Theorems.Thm_WilliamsonShmoys_edgeFinset_card_le_edgeSet_ncard_of_subset__p2m_a34ee183_b91b_4a67_873f_251f94ba9522_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    G.edgeFinset.card + 6 <= 3 * Fintype.card V := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hbound :
      G.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
    WilliamsonShmoys.planar_edge_count_upper_bound_938af664_b2aa_4ceb_8ad4_a78c6b3943d3
      G hV hG
  have hedge :
      G.edgeFinset.card <= G.edgeSet.ncard :=
    WilliamsonShmoys.edgeFinset_card_le_edgeSet_ncard_of_subset__p2m_a34ee183_b91b_4a67_873f_251f94ba9522_a2
      G G (by intro e he; exact he)
  omega