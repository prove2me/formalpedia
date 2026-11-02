-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_8e688b5a_4cd6_4a71_af1c_8dd5b2ac94c3_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:57:41.676463+00:00
-- url     : https://prove2.me/submissions/54fdde27-7072-489e-a941-9ce3f997a2cd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_8a171377_f33b_49cc_b27f_3a0a7f3acd0d_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_8a171377_f33b_49cc_b27f_3a0a7f3acd0d_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 ≤ Fintype.card V)
    (hmax : ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn L →
      K.edgeFinset ⊆ L.edgeFinset → K.edgeFinset = L.edgeFinset) :
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  have h_lower := WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_8a171377_f33b_49cc_b27f_3a0a7f3acd0d_a1
    K dK hK hn hmax
  have h_upper := WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_8a171377_f33b_49cc_b27f_3a0a7f3acd0d_a1
    K dK hK hn
  omega