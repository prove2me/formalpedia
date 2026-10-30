-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_b3dab4f4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:43:36.982282+00:00
-- url     : https://prove2.me/submissions/aa173706-b252-4ab2-b9e6-cf3af80d55b6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_ge__p2m_6af46978_2916_4816_b606_4f4cb75b2f24_a1

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V, L <= M ->
      WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) :
    3 * Fintype.card V - 6 <= L.edgeSet.ncard := by
  first
  | exact _root_.WilliamsonShmoys.maximal_planar_edge_count_ge__p2m_6af46978_2916_4816_b606_4f4cb75b2f24_a1
  | (apply _root_.WilliamsonShmoys.maximal_planar_edge_count_ge__p2m_6af46978_2916_4816_b606_4f4cb75b2f24_a1 <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.maximal_planar_edge_count_ge__p2m_6af46978_2916_4816_b606_4f4cb75b2f24_a1 <;> assumption)
