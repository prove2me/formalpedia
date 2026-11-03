-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_cc6eda38_1b75_4537_8542_c84b46a8d9a9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:52:56.47658+00:00
-- url     : https://prove2.me/submissions/f02d913e-ff83-4ee1-99ce-81a1d6948417

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph__p2m_fba5509b_7521_41eb_ae0d_1c68b4ac0c26_a1

set_option autoImplicit false

open scoped BigOperators

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ L : SimpleGraph V, H ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hHL, hL, hcount⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_supergraph__p2m_fba5509b_7521_41eb_ae0d_1c68b4ac0c26_a1
      H hcard hH
  have hLH : L = H := hmax L hHL hL
  simpa [hLH] using hcount