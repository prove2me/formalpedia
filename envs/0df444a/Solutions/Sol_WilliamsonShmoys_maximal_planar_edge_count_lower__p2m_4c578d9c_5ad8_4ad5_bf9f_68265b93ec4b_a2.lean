-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_4c578d9c_5ad8_4ad5_bf9f_68265b93ec4b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:34:21.039809+00:00
-- url     : https://prove2.me/submissions/0e256259-6de8-4b3e-b4f0-fddaba525871

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_fc016acd_24e0_4b4c_9f94_11715a39d633

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_planar_edge_count_lower_bound_fc016acd_24e0_4b4c_9f94_11715a39d633 K hK hV hmax
