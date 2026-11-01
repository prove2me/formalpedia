-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_edge_bound__p2m_9339270d_9fc9_4b81_a23b_72e2e50fd8a3_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:39:51.022375+00:00
-- url     : https://prove2.me/submissions/bca393aa-8dee-4a08-8b4a-944a1e7ad9a4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_extension_edge_bound__p2m_06807de4_e70a_4ffd_9441_1bb5fb02d634_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      (∀ u v, K.Adj u v → L.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hBound⟩ :=
    WilliamsonShmoys.planar_extension_edge_bound__p2m_06807de4_e70a_4ffd_9441_1bb5fb02d634_a1
      K hCard hK
  have hEq : L = K := hMax L hKL hL
  simpa [hEq] using hBound
