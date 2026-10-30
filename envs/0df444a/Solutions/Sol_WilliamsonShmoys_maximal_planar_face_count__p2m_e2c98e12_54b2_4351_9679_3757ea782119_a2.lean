-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_count__p2m_e2c98e12_54b2_4351_9679_3757ea782119_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:41:22.679187+00:00
-- url     : https://prove2.me/submissions/730dcbcb-f278-432e-819e-566389e7ab10
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_lower_edge_bound__p2m_e138972d_9fa2_4192_8bee_87ee7300d413_a2
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_upper_bound__p2m_e138972d_9fa2_4192_8bee_87ee7300d413_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ->
      Set.Subset H.edgeSet K.edgeSet ->
      H.edgeSet = K.edgeSet)
    (hV : 3 <= Fintype.card V) :
    Exists fun f : Nat =>
      And (Fintype.card V + f = H.edgeSet.ncard + 2)
          (3 * f = 2 * H.edgeSet.ncard) := by
  have hlow :=
    WilliamsonShmoys.maximal_planar_lower_edge_bound__p2m_e138972d_9fa2_4192_8bee_87ee7300d413_a2
      H hH hmax hV
  have hupp :=
    WilliamsonShmoys.planar_simple_edge_upper_bound__p2m_e138972d_9fa2_4192_8bee_87ee7300d413_a2
      H hH hV
  have hm : H.edgeSet.ncard = 3 * Fintype.card V - 6 :=
    Nat.le_antisymm hupp hlow
  refine Exists.intro (2 * Fintype.card V - 4) (And.intro ?_ ?_) <;> omega