-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_1591b9cd_ac13_4639_82d2_61e7ddbdd660
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:06:58.812586+00:00
-- url     : https://prove2.me/submissions/5b122e7e-0155-432a-a974-7a8ae827f294

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_finite_property_f877e9d9

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ J : SimpleGraph V, H ≤ J →
        WilliamsonShmoys.HasPlanarDrawingOn J → J = H) ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact WilliamsonShmoys.exists_maximal_supergraph_for_finite_property_f877e9d9
    (P := WilliamsonShmoys.HasPlanarDrawingOn) K hK