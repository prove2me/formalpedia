-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_c00979a8
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:12:49.158083+00:00
-- url     : https://prove2.me/submissions/2e24942e-6ecd-4ec7-9eeb-205b8a7760af

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_c00979a8_planar_edge_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_c00979a8_maximal_lower_bound

set_option autoImplicit false

 theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K <= L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  have hupper := WilliamsonShmoys.maximal_planar_drawing_edge_count_c00979a8_planar_edge_bound K hV hK
  have hlower := WilliamsonShmoys.maximal_planar_drawing_edge_count_c00979a8_maximal_lower_bound K hV hK hmax
  omega