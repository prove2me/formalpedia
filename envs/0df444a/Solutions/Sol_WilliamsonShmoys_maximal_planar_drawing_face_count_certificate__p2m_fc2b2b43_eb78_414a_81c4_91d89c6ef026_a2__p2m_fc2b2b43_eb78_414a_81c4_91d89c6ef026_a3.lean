-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_face_count_certificate__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a2__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:31:35.051616+00:00
-- url     : https://prove2.me/submissions/26a0330c-9ffc-47a7-bf97-de8827ffa3ce

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_6a44195f_ae15_4a06_a6fa_fb89b3d5738f_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V)
    (hmax : forall H : SimpleGraph V, K <= H -> WilliamsonShmoys.HasPlanarDrawingOn H -> H <= K) :
    exists f : Nat, Fintype.card V + f = K.edgeSet.ncard + 2 /\ 3 * f = 2 * K.edgeSet.ncard := by
  have hE := WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_6a44195f_ae15_4a06_a6fa_fb89b3d5738f_a1 K hK hV hmax
  refine Exists.intro (2 * Fintype.card V - 4) ?_
  constructor <;> omega