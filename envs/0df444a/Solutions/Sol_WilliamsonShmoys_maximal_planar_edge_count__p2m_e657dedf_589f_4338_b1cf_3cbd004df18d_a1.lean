-- Prove2me | solution 1 for WilliamsonShmoys_maximal_planar_edge_count__p2m_e657dedf_589f_4338_b1cf_3cbd004df18d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:23:01.59277+00:00
-- url     : https://prove2.me/submissions/70206a91-f217-4dd3-bc72-8ac011815c93
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_upper_bound__p2m_2094dec4_72bc_4506_8cb1_28494e96e3ad_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_2094dec4_72bc_4506_8cb1_28494e96e3ad_a1
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hconn : K.Connected)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys_planar_simple_edge_upper_bound__p2m_2094dec4_72bc_4506_8cb1_28494e96e3ad_a1
    (V := V) K hV hK
  have hlower := WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_2094dec4_72bc_4506_8cb1_28494e96e3ad_a1
    (V := V) K hV hconn hK hmax
  omega