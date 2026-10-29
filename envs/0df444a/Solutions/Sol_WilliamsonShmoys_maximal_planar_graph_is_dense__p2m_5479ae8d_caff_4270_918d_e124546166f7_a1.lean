-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_is_dense__p2m_5479ae8d_caff_4270_918d_e124546166f7_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T23:12:04.409507+00:00
-- url     : https://prove2.me/submissions/e997ec80-3e42-40a2-88ce-d9c1aeb24353
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_exact_edge_count__p2m_48acce6a_8f33_48c6_a9d8_ff0d2e5ac6c0_a3

set_option autoImplicit false

open SimpleGraph

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, N ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ N) :
    3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by
  obtain ⟨M, hNM, hM, hCount⟩ :=
    WilliamsonShmoys.exists_planar_supergraph_exact_edge_count__p2m_48acce6a_8f33_48c6_a9d8_ff0d2e5ac6c0_a3
      N hN hV
  have hEq : N = M := le_antisymm hNM (hmax M hNM hM)
  rw [hEq]
  exact le_of_eq hCount.symm