-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_abcc1e5a_cabd_49d6_8da8_bf017a643b84_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:36:46.087955+00:00
-- url     : https://prove2.me/submissions/547551c9-c7f0-43b8-956c-d14943ea9a1f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_with_triangulated_edge_count__p2m_ff88384e_13a7_4e55_8777_790088f23a4a_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet = L.edgeSet) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hM, hcount⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_with_triangulated_edge_count__p2m_ff88384e_13a7_4e55_8777_790088f23a4a_a2
      L hcard hL
  have hEq := hmax M hLM hM
  rw [hEq] at hcount
  omega