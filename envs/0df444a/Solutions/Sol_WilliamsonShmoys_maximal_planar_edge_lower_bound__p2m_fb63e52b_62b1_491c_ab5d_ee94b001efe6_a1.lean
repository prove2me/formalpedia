-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_fb63e52b_62b1_491c_ab5d_ee94b001efe6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:40:23.904767+00:00
-- url     : https://prove2.me/submissions/322ff2ca-ff81-4318-a5c9-aa7c4a8bd1f1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_bound__p2m_4df8ba81_9f07_4595_bdbe_b174d2b4360b_a3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V,
      H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = H)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    3 * Fintype.card V <= H.edgeFinset.card + 6 := by
  classical
  obtain ⟨K, hHK, hK, hbound⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_bound__p2m_4df8ba81_9f07_4595_bdbe_b174d2b4360b_a3 H hH hcard
  have hEq : K = H := hmax K hHK hK
  cases hEq
  exact hbound