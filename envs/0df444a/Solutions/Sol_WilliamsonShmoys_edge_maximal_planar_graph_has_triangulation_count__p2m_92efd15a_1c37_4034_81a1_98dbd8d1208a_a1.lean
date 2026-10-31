-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_graph_has_triangulation_count__p2m_92efd15a_1c37_4034_81a1_98dbd8d1208a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:02:58.640989+00:00
-- url     : https://prove2.me/submissions/3b35fd27-e177-488b-99a6-b39e25b92f36

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_triangulation_supergraph_exact_edge_count__p2m_c4417236_d2c3_4bc2_b2ac_88bc17b75d38_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V - 6 = K.edgeSet.ncard := by
  obtain ⟨L, hKL, hLdraw, hLcount⟩ :=
    WilliamsonShmoys.drawable_triangulation_supergraph_exact_edge_count__p2m_c4417236_d2c3_4bc2_b2ac_88bc17b75d38_a1
      K hV hK
  have hLK : L = K := hmax L hKL hLdraw
  rw [← hLK]
  exact hLcount