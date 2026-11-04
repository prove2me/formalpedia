-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_8a171377_f33b_49cc_b27f_3a0a7f3acd0d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:15:45.247164+00:00
-- url     : https://prove2.me/submissions/f00751eb-8135-4cf5-a066-c183a88e5b17

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_c3c9ffa7_0ab4_4781_8a7b_d6d91ceb974a_a3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 <= Fintype.card V)
    (hmax : forall (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn L ->
      K.edgeFinset ⊆ L.edgeFinset -> K.edgeFinset = L.edgeFinset) :
    3 * Fintype.card V - 6 <= K.edgeFinset.card := by
  obtain ⟨L, dL, hL, hsub, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_c3c9ffa7_0ab4_4781_8a7b_d6d91ceb974a_a3
      K dK hK hn
  have heq : K.edgeFinset = L.edgeFinset := hmax L dL hL hsub
  rw [heq, hcount]