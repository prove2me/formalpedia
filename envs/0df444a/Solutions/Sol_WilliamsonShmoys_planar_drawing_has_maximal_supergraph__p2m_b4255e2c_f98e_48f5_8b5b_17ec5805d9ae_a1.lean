-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_b4255e2c_f98e_48f5_8b5b_17ec5805d9ae_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:26:08.629988+00:00
-- url     : https://prove2.me/submissions/25f4cbc3-c6ea-4a27-b30e-1d90df41a942

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_exists_maximal_extension_of_finite_edges__p2m_724a012f_3099_4ee5_9840_4b16b095fdb5_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ T : SimpleGraph V, M ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      (∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ T) := by
  exact exists_maximal_extension_of_finite_edges__p2m_724a012f_3099_4ee5_9840_4b16b095fdb5_a1
    WilliamsonShmoys.HasPlanarDrawingOn M hDraw