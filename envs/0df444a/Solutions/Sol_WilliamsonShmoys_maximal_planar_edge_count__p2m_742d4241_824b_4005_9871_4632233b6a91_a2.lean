-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_742d4241_824b_4005_9871_4632233b6a91_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T18:35:32.898425+00:00
-- url     : https://prove2.me/submissions/80eafcd9-ec97-4764-a31e-21ab9d3b4cb1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_upper_bound__p2m_b2020b19_fb40_461e_a788_a72b44070de7_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_lower_bound__p2m_b2020b19_fb40_461e_a788_a72b44070de7_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.maximal_planar_upper_bound__p2m_b2020b19_fb40_461e_a788_a72b44070de7_a2
      K hK hV
  · exact WilliamsonShmoys.maximal_planar_lower_bound__p2m_b2020b19_fb40_461e_a788_a72b44070de7_a2
      K hK hmax hV