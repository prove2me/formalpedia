-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_inclusion_maximal_drawable__p2m_6e736750_a362_4363_844e_e38c08b33ed2_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:58:57.544433+00:00
-- url     : https://prove2.me/submissions/b42a8ed9-efa3-44f8-88bc-cf8211b54c9b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_0d663055_40d3_4575_b5af_11ff2bc59459_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_lower_bound__p2m_0d663055_40d3_4575_b5af_11ff2bc59459_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (L : SimpleGraph V) (_hLdec : DecidableRel L.Adj),
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_edge_count_upper_bound__p2m_0d663055_40d3_4575_b5af_11ff2bc59459_a1 K hK hcard
  · exact WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_0d663055_40d3_4575_b5af_11ff2bc59459_a1 K hK hcard hmax