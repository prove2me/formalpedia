-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_10fbf93e_9f1f_430c_8d69_9a023f7a87fc_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:30:07.196829+00:00
-- url     : https://prove2.me/submissions/ac531dc7-97a0-4c42-a1d1-1a29729ec339
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_8d6b5728_c6cc_4920_a7cd_a91520c68320_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_8d6b5728_c6cc_4920_a7cd_a91520c68320_a1
import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K →
      N.edgeFinset ⊆ K.edgeFinset →
      K.edgeFinset ⊆ N.edgeFinset) :
    N.edgeFinset.card = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_8d6b5728_c6cc_4920_a7cd_a91520c68320_a1 N dN hN hcard
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_8d6b5728_c6cc_4920_a7cd_a91520c68320_a1 N dN hN hcard hmax
  omega