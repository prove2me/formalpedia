-- Prove2me | solution 2 for WilliamsonShmoys.planar_triangulation_supergraph_edge_count__p2m_c52ee0f6_cd77_40cf_a2f0_4d029ef0159f_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T19:59:32.142717+00:00
-- url     : https://prove2.me/submissions/aea74dca-d084-4c25-a384-850f4b93a8ef

import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_0d3ba6cc_be4a_436c_b614_289a3ecc8076_a1
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_triangulation_completion__p2m_0d3ba6cc_be4a_436c_b614_289a3ecc8076_a1 K hK hcard