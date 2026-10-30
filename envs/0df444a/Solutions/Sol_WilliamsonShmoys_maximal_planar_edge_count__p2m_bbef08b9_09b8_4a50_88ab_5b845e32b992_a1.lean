-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_bbef08b9_09b8_4a50_88ab_5b845e32b992_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:52:18.004317+00:00
-- url     : https://prove2.me/submissions/869a9eca-7460-45af-8a9b-02e2782e7d88

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M.edgeSet ⊆ N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hN, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count M hV hM
  have hSub : M.edgeSet ⊆ N.edgeSet := SimpleGraph.edgeSet_mono hMN
  have hEq : N = M := hMax N hSub hN
  subst N
  exact hCount.symm