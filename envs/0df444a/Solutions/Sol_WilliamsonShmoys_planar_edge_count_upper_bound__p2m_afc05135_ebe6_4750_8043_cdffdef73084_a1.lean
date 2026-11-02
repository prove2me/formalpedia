-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_afc05135_ebe6_4750_8043_cdffdef73084_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T23:19:18.250999+00:00
-- url     : https://prove2.me/submissions/45a5b591-3917-4349-b9a2-a6faac6e7872

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_38a90fc3_dea3_4c9f_8a52_b5002f138593_a1
import Theorems.Thm_WilliamsonShmoys_edgeFinset_card_le_edgeSet_ncard_of_subset__p2m_a34ee183_b91b_4a67_873f_251f94ba9522_a2
import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 <= 3 * Fintype.card V) := by
  classical
  have hplanar :
      H.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
    WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_38a90fc3_dea3_4c9f_8a52_b5002f138593_a1
      H hcard hdraw
  have hcount : H.edgeFinset.card <= H.edgeSet.ncard :=
    WilliamsonShmoys.edgeFinset_card_le_edgeSet_ncard_of_subset__p2m_a34ee183_b91b_4a67_873f_251f94ba9522_a2
      H H (fun _ he => he)
  exact (Nat.add_le_add_right hcount 6).trans hplanar
