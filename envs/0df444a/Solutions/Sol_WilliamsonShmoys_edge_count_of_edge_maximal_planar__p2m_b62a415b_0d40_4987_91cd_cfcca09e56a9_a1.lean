-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_edge_maximal_planar__p2m_b62a415b_0d40_4987_91cd_cfcca09e56a9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T00:11:45.179046+00:00
-- url     : https://prove2.me/submissions/ee76054e-1663-4557-8e76-1cbe6494f90f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_exact_edge_count__p2m_27144f45_411a_4982_b72d_bbbc3f64b45b_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V, H <= K ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> K = H)
    (hcard : 3 <= Fintype.card V) :
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by
  classical
  have hncard :=
    WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count__p2m_27144f45_411a_4982_b72d_bbbc3f64b45b_a1
      H hH hcard hmax
  have hfinite : H.edgeSet.Finite := Set.toFinite H.edgeSet
  have hto : hfinite.toFinset = H.edgeFinset := by
    ext e
    simp [SimpleGraph.edgeFinset]
  have hedge : H.edgeSet.ncard = H.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card H.edgeSet hfinite, hto]
  rw [hedge] at hncard
  omega
