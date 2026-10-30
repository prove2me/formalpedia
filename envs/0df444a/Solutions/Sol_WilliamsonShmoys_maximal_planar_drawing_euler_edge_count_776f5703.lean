-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_euler_edge_count_776f5703
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:15:12.238616+00:00
-- url     : https://prove2.me/submissions/0bd2ad83-6554-41e3-bd26-0272cacd3c09

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_upper_edge_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_euler_lower_edge_bound
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper :=
    WilliamsonShmoys.planar_drawing_euler_upper_edge_bound K hV hK
  have hlower :=
    WilliamsonShmoys.maximal_planar_drawing_euler_lower_edge_bound
      K hV hK hmax
  omega
