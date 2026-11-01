-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_0d663055_40d3_4575_b5af_11ff2bc59459_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:05:54.44955+00:00
-- url     : https://prove2.me/submissions/568f469a-63bc-4edf-b462-413ec878b84e

import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_exact_edge_count__p2m_dafc9680_9370_4a7d_835c_8ab6494e7297_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hsub, hHplanar, hKle, hHcard⟩ :=
    WilliamsonShmoys.planar_drawing_completion_exact_edge_count__p2m_dafc9680_9370_4a7d_835c_8ab6494e7297_a2
      K hcard hK
  omega
