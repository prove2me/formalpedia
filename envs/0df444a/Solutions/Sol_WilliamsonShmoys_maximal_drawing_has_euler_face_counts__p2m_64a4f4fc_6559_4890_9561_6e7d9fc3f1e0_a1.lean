-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_has_euler_face_counts__p2m_64a4f4fc_6559_4890_9561_6e7d9fc3f1e0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:23:59.869852+00:00
-- url     : https://prove2.me/submissions/9aba6435-71f7-474a-a14e-ebb56abcbf9c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_a7a27be2_fbb8_44ae_9ce4_aea6abd1f255_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V)
    (hmax : forall H : SimpleGraph V, K <= H -> WilliamsonShmoys.HasPlanarDrawingOn H -> H <= K) :
    Exists fun f : Nat => And
      (Fintype.card V + f = K.edgeSet.ncard + 2)
      (3 * f = 2 * K.edgeSet.ncard) := by
  have hE := WilliamsonShmoys.maximal_planar_edge_count__p2m_a7a27be2_fbb8_44ae_9ce4_aea6abd1f255_a1
    K hK hV hmax
  refine Exists.intro (2 * Fintype.card V - 4) ?_
  constructor <;> omega