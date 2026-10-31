-- Prove2me | solution 1 for WilliamsonShmoys.drawable_triangulation_supergraph_exact_edge_count__p2m_c4417236_d2c3_4bc2_b2ac_88bc17b75d38_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:21:35.444967+00:00
-- url     : https://prove2.me/submissions/53d74090-d8c5-40ee-9cfa-2f735a740fe8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_triangulation_maximal_extension__p2m_ec7a7294_2e22_40b0_b436_8d0de67c32fd_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_ec7a7294_2e22_40b0_b436_8d0de67c32fd_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V - 6 = L.edgeSet.ncard := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.drawable_triangulation_maximal_extension__p2m_ec7a7294_2e22_40b0_b436_8d0de67c32fd_a1
      K hV hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_drawable_edge_count__p2m_ec7a7294_2e22_40b0_b436_8d0de67c32fd_a1
      L hV hL hmax⟩