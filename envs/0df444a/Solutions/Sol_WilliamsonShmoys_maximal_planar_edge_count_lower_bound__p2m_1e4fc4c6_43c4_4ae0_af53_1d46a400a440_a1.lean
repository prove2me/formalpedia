-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_1e4fc4c6_43c4_4ae0_af53_1d46a400a440_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:16:41.538992+00:00
-- url     : https://prove2.me/submissions/0cada3f5-8423-4057-84fe-5098a85a7ce9

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_c9a3871e_5cc1_4338_ae1f_e59bec6b3362_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) (hCard : 3 ≤ Fintype.card V) (hmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K ≤ N) : 3 * Fintype.card V - 6 ≤ N.edgeSet.ncard :=
  WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c9a3871e_5cc1_4338_ae1f_e59bec6b3362_a1 N hN hCard hmax
