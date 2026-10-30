-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_d974173a
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:25:28.476414+00:00
-- url     : https://prove2.me/submissions/2e153772-c179-491b-b556-b9ef427c65eb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_upper_bound_d974173a
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_lower_bound_d974173a

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  have hup := WilliamsonShmoys.maximal_drawable_edge_upper_bound_d974173a
    K hdraw hV
  have hlo := WilliamsonShmoys.maximal_drawable_edge_lower_bound_d974173a
    K hdraw hV hmax
  omega