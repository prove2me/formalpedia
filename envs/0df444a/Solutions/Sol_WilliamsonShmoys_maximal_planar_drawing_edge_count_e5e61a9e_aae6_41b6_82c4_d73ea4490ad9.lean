-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_e5e61a9e_aae6_41b6_82c4_d73ea4490ad9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:58:26.507626+00:00
-- url     : https://prove2.me/submissions/5f760b2f-a317-47fc-8caf-521d22129dc9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_planar_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_maximal_lower_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.maximal_planar_drawing_edge_count_planar_upper_bound
      K hV hdraw
  · exact WilliamsonShmoys.maximal_planar_drawing_edge_count_maximal_lower_bound
      K hV hdraw hconn hmax