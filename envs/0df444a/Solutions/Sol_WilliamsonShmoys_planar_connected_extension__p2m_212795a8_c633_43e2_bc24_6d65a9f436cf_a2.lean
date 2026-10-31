-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_extension__p2m_212795a8_c633_43e2_bc24_6d65a9f436cf_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:47:40.219997+00:00
-- url     : https://prove2.me/submissions/e22c57fe-fb86-49df-b6e5-b29963e834a1

import Theorems.Thm_WilliamsonShmoys_exists_connected_planar_supergraph_for_edge_bound_30a2cd75__p2m_66e594d2_cb5c_4a09_8145_3dd71ccc0d91_a3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected :=
  WilliamsonShmoys.exists_connected_planar_supergraph_for_edge_bound_30a2cd75__p2m_66e594d2_cb5c_4a09_8145_3dd71ccc0d91_a3 K hK hV
